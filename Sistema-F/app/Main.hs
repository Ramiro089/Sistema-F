module Main ( main )
where

import qualified Control.Monad.Catch     as MC
import qualified Data.Set                as Set
import           Control.Monad.Except
import           Data.Char
import           Data.List                      ( isPrefixOf, intercalate )
import           Data.Maybe
import           Prelude                 hiding ( print )
import           System.Console.Haskeline
import           System.Environment
import           System.IO               hiding ( print )
import           Text.PrettyPrint.HughesPJ      ( render, text )
import           Control.Monad.Trans
import           Common
import           PrettyPrinter
import           SystemF
import           Parse

-- Esta función se usa solo si el comando seleccionado es :browse
-- Antes usaba el nub definido por defecto, pero este era de costo O(n^2)
-- Con esta nueva forma el costo del nub es de O(n.lg(n)) 
myNub :: Ord a => [a] -> [a]
myNub = aux Set.empty
  where aux _ [] = []
        aux ys (x:xs) | Set.member x ys = aux ys xs
                      | otherwise       = x : aux (Set.insert x ys) xs

------------------------------------------
newtype State = S { ve :: NameEnv Value Type }

data Command = Quit
             | None
             | Help
             | Browse
             | Compile String
             | Print String
             | Type String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- Ejecuta el interprete del Sistema F
main :: IO ()
main = runInputT defaultSettings $
       do args <- lift getArgs
          iteration args (S [])

-- Se encarga de generar el loop de interacción
iteration :: [String] -> State -> InputT IO ()
iteration args state@(S ve) =
  let rec st = do mx <- MC.catchIOError (getInputLine "SF> ") (\_ -> lift (return Nothing))
                  case mx of
                    Nothing -> return ()
                    Just "" -> rec st
                    Just x  -> do c   <- interpretCommand x
                                  st' <- handleCommand st c
                                  maybe (return ()) rec st'
  in do lift $ putStrLn ("\n" ++ "Intérprete de Sistema F" ++ "\n" ++ "Escriba :help para ver los comandos")
        rec state

-- Se encarga de procesar la entrada y verificar que el comando sea valido
interpretCommand :: String -> InputT IO Command
interpretCommand x = lift $ if ":" `isPrefixOf` x
  then do let (cmd, t') = break isSpace x
          let t         = dropWhile isSpace t'
          let matching  = filter (\(Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
          case matching of
            [Cmd _ _ f _] -> do return (f t)
            _             -> do putStrLn ("Comando desconocido '" ++ cmd ++ "'. Escriba :help para ver los comandos.")
                                return None
  else return (Compile x)

-- En base al comando de entrada selecciona la acción a realizar, utilizando el estado actual
handleCommand :: State -> Command -> InputT IO (Maybe State)
handleCommand state@(S ve) cmd =
  case cmd of
    Quit      -> lift $ return Nothing
    None      -> return (Just state)
    Help      -> lift $ putStr (helpTxt commands) >> return (Just state)
    Browse    -> lift $ do putStr (unlines (reverse (myNub (map fst ve))))
                           return (Just state)
    Compile s -> do state' <- compilePhrase state s
                    return (Just state')
    Print s   -> let s' = reverse (dropWhile isSpace (reverse (dropWhile isSpace s)))
                 in printPhrase s' >> return (Just state)
    Type s    -> do x' <- parseIO term s
                    t  <- case x' of
                            Nothing -> return $ Left "Error en el parsing."
                            Just x  -> return $ infer ve $ conversion x
                    case t of
                      Left  err -> lift (putStrLn ("Error de tipos: " ++ err)) >> return ()
                      Right t'  -> lift $ putStrLn $ render $ printType t'
                    return (Just state)

commands :: [InteractiveCommand]
commands = [Cmd [":browse"] ""       (const Browse) "Ver los nombres en scope \n",
            Cmd [":print"]  "<exp>"  Print          "Imprime un término y sus ASTs \n",
            Cmd [":quit"]   ""       (const Quit)   "Salir del intérprete \n",
            Cmd [":help"]   ""       (const Help)   "Muestra una lista de comandos \n",
            Cmd [":type"]   "<term>" Type           "Inferir el tipo del término \n"]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs = "--------------------------------------------------\n"
    ++ "·····················COMANDOS·····················\n"
    ++ "--------------------------------------------------\n"
    ++ "Los comando se pueden abreviar como :c donde\n"
    ++ "c es el primer carácter del nombre completo.\n\n"
    ++ "<expr>                  Evaluar expresión\n"
    ++ "def <var> = <expr>      Definir una variable\n"
    ++ concatMap (\(Cmd c a _ d) -> let ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                                    in  ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs

-- Se encarga de parsear un string y procesarlo (en la función handleStmt)
compilePhrase :: State -> String -> InputT IO State
compilePhrase state x = do x' <- parseIO parseStmt x
                           maybe (return state) (handleStmt state) x'

-- Se encarga de parsear un string, convertirlo a un Term e imprimirlo
printPhrase :: String -> InputT IO ()
printPhrase x = do x' <- parseIO parseStmt x
                   maybe (return ()) (printStmt . fmap (\y -> (y, conversion y))) x'

-- Imprime por pantalla cuando se usa el comando :print
printStmt :: Stmt (LamTerm, Term) -> InputT IO ()
printStmt stmt = lift $ do let printText = case stmt of
                                 Def x (_, e) -> "def " ++ x ++ " = " ++ render (printTerm e)
                                 Eval (d, e)  -> "AST LamTerm:\n"
                                                   ++ show d
                                                   ++ "\n\nAST Term:\n"
                                                   ++ show e
                                                   ++ "\n\nSe muestra como:\n"
                                                   ++ render (printTerm e)
                           putStrLn printText

-- Parsea un string, se le pasa el parser a usar. Si no hay problema devuelve el resultado, caso contrario muestra un error por pantalla 
parseIO :: (String -> ParseResult a) -> String -> InputT IO (Maybe a)
parseIO p x = lift $ case p x of
                        Failed e -> do putStrLn e
                                       return Nothing
                        Ok r -> return (Just r)

-- Procesa un "lambda termino", chequeadolo y evaluándolo. Def y Eval actualizan el estado, pero Eval siempre actualiza el mismo.
handleStmt :: State -> Stmt LamTerm -> InputT IO State
handleStmt state stmt = lift $ do case stmt of
                                    Def x e -> checkType x (conversion e)
                                    Eval e  -> checkType "LastInput" (conversion e)
 where
  checkType i t = do case infer (ve state) t of
                       Left err -> putStrLn ("Error de tipos: " ++ err) >> return state
                       Right ty -> checkEval i t ty
  checkEval i t ty = do let v = eval (ve state) t
                        _ <- do putStrLn $ if i == "LastInput" then render (printTerm (quote v)) else render (text i)
                        return (state { ve = (i, (v, ty)) : ve state })