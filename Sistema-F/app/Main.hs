module Main where

import           Control.Exception              ( catch, IOException )
import           Control.Monad.Except
import           Data.Char
import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( print )
import           System.Console.Haskeline
import qualified Control.Monad.Catch     as MC
import           System.Environment
import           System.IO               hiding ( print )
import           Text.PrettyPrint.HughesPJ      ( render, text )
import           Control.Monad.Trans
import           Control.Monad.IO.Class         ( liftIO )
import           Control.Monad                  ( foldM, when )
import           Common
import           PrettyPrinter
import           SystemF
import           Parse

data State = S { ve :: NameEnv Value Type }

data Command = Compile String
             | Print String
             | Browse
             | Quit
             | Help
             | Noop
             | FindType String

data InteractiveCommand = Cmd [String] String (String -> Command) String

main :: IO ()
main = runInputT defaultSettings $ 
       do args <- lift getArgs
          readevalprint args (S [])

ioExceptionCatcher :: IOException -> IO (Maybe a)
ioExceptionCatcher _ = return Nothing

-- Se encarga de generar el loop de interacción
readevalprint :: [String] -> State -> InputT IO ()
readevalprint args state@(S ve) =
  let rec st = do mx <- MC.catch
                    (getInputLine "SF> ")
                    (lift . ioExceptionCatcher)
                  case mx of
                    Nothing -> return ()
                    Just "" -> rec st
                    Just x  -> do c   <- interpretCommand x
                                  st' <- handleCommand st c
                                  maybe (return ()) rec st'
  in do lift $ putStrLn ("Intérprete de " ++ "Sistema F" ++ "\n" ++ "Escriba :help para ver los comandos")
        rec state

-- Se encarga de procesar la entrada y verificar que el comando sea valido y no ambiguo
interpretCommand :: String -> InputT IO Command
interpretCommand x = lift $ if isPrefixOf ":" x
  then do let (cmd, t') = break isSpace x
          let t         = dropWhile isSpace t'
          let matching  = filter (\(Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
          case matching of
            [] -> do putStrLn ("Comando desconocido '" ++ cmd ++ "'. Escriba :help para ver los comandos.")
                     return Noop
            [Cmd _ _ f _] -> do return (f t)
            _ -> do putStrLn ("Comando ambigüo, podría ser " ++ concat (intersperse ", " [ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                    return Noop
  else return (Compile x)

-- En base al comando de entrada selecciona la acción a realizar
handleCommand :: State -> Command -> InputT IO (Maybe State)
handleCommand state@(S ve) cmd = 
  case cmd of
      Quit   -> lift $ return Nothing
      Noop   -> return (Just state)
      Help   -> lift $ putStr (helpTxt commands) >> return (Just state)
      Browse -> lift $ do putStr (unlines [ s | Global s <- reverse (nub (map fst ve)) ])
                          return (Just state)
      Compile s -> do state' <- compilePhrase state s
                      return (Just state')
      Print s -> let s' = reverse (dropWhile isSpace (reverse (dropWhile isSpace s)))
                 in printPhrase s' >> return (Just state)
      FindType s -> do x' <- parseIO term_parse s
                       t  <- case x' of
                               Nothing -> return $ Left "Error en el parsing."
                               Just x  -> return $ infer ve $ conversion $ x
                       case t of
                         Left  err -> lift (putStrLn ("Error de tipos: " ++ err)) >> return ()
                         Right t'  -> lift $ putStrLn $ render $ printType t'
                       return (Just state)

commands :: [InteractiveCommand]
commands =
  [ Cmd [":browse"] ""       (const Browse) "Ver los nombres en scope"
  , Cmd [":print"]  "<exp>"  Print          "Imprime un término y sus ASTs"
  , Cmd [":quit"]   ""       (const Quit)   "Salir del intérprete"
  , Cmd [":help"]   ""       (const Help)   "Muestra una lista de comandos"
  , Cmd [":type"]   "<term>" (FindType)     "Inferir el tipo del término"
  ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs =
  "--------------------------------------------------\n" 
    ++ "·····················COMANDOS·····················\n"
    ++ "--------------------------------------------------\n"
    ++ "Los comando se pueden abreviar como :c donde\n"
    ++ "c es el primer caracter del nombre completo.\n\n"
    ++ "<expr>                  Evaluar expresión\n"
    ++ "def <var> = <expr>      Definir una variable\n"
    ++ unlines
         (map
           (\(Cmd c a _ d) -> let ct = concat(intersperse ", " (map (++ if null a then "" else " " ++ a) c))
                              in  ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d)
           cs)

-- Se encarga de parsear un string y procesarlo (en la funcion handleStmt)
compilePhrase :: State -> String -> InputT IO State
compilePhrase state x = do x' <- parseIO stmt_parse x
                           maybe (return state) (handleStmt state) x'

-- Se encarga de parsear un string, convertirlo e imprimirlo
printPhrase :: String -> InputT IO ()
printPhrase x = do x' <- parseIO stmt_parse x
                   maybe (return ()) (printStmt . fmap (\y -> (y, conversion y))) x'

-- Imprime por pantalla cuando se usa el comando :print
printStmt :: Stmt (LamTerm, Term) -> InputT IO ()
printStmt stmt = lift $ do let outtext = case stmt of
                                 Def x (_, e) -> "def " ++ x ++ " = " ++ render (printTerm e)
                                 Eval (d, e)  -> "LamTerm AST:\n"
                                                   ++ show d
                                                   ++ "\n\nTerm AST:\n"
                                                   ++ show e
                                                   ++ "\n\nSe muestra como:\n"
                                                   ++ render (printTerm e)
                           putStrLn outtext

-- Parsea un string
-- SI no hay problema devuelve el resultado del análisis, caso contrario muestra un error por pantalla 
parseIO :: (String -> ParseResult a) -> String -> InputT IO (Maybe a)
parseIO p x = lift $ case p x of
                        Failed e -> do putStrLn e
                                       return Nothing
                        Ok r -> return (Just r)

-- Procesa un "lamda termino"
-- El cual es chequeado y evaluado. Si es un Def infiere el tipo, si es un Eval evalúa la expresión
handleStmt :: State -> Stmt LamTerm -> InputT IO State
handleStmt state stmt = lift $ do case stmt of
                                    Def x e -> checkType x (conversion e)
                                    Eval e  -> checkType "LastInput" (conversion e)
 where
  checkType i t = do case infer (ve state) t of
                       Left  err -> putStrLn ("Error de tipos: " ++ err) >> return state
                       Right ty  -> checkEval i t ty
  checkEval i t ty = do let v = eval (ve state) t
                        _ <- do let outtext = if i == "LastInput" then render (printTerm (quote v)) else render (text i)
                                putStrLn outtext
                        return (state { ve = (Global i, (v, ty)) : ve state })