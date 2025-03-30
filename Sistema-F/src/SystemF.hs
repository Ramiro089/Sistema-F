{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module SystemF ( conversion, eval, infer, quote )
where

import           Data.List                  ( elemIndex, elemIndices )
import           Data.Maybe                 ( fromJust, fromMaybe, maybe )
import           Prelude
import           Text.PrettyPrint.HughesPJ  ( render )
import           PrettyPrinter
import           Common

-- Convierte un LamTerm a un Term, aplicando una función de conversion
toTerm:: (LamTerm -> Term) -> LamTerm -> [String] -> Term
toTerm f (LAbs name typee t) c = Lam (conversionType typee c) $ f t
toTerm f (LApp t1 t2) _        = f t1 :@: f t2

-- Sistema F
toTerm f (LTAbs name t)  _ = ForAll (f t)
toTerm f (LTApp t typee) c = TApp (f t) (conversionType typee c)

-- Bool
toTerm f LTrue _  = T
toTerm f LFalse _ = F
toTerm f (LIfThenElse t1 t2 t3) _ = IfThenElse (f t1) (f t2) (f t3)

-- Nat
toTerm f LZero _           = Zero
toTerm f (LSuc t) _        = Suc $ f t
toTerm f (LRec t1 t2 t3) _ = Rec (f t1) (f t2) (f t3)

-- List
toTerm f LNil _             = Nil
toTerm f (LCons t1 t2) _    = Cons (f t1) (f t2)
toTerm f (LRecL t1 t2 t3) _ = RecL (f t1) (f t2) (f t3)

toTerm f t _ = error $ "No se puede convertir el lambda termino " ++ show t ++ " a un termino"

-- Conversion a Term
conversion :: LamTerm -> Term
conversion = conversion' [] []

conversion' :: [String] -> [String] -> LamTerm -> Term
conversion' vars cuan (LVar name)            = maybe (Free (Global name)) Bound (elemIndex name vars)
conversion' vars cuan t@(LAbs name _ _)      = toTerm (conversion' (name:vars) cuan) t cuan
conversion' vars cuan t@(LTAbs name lamTerm) = toTerm (conversion' vars (cuan ++ [name])) t cuan
conversion' vars cuan t                      = toTerm (conversion' vars cuan) t cuan

---------------------------------
{-
La idea de esta función es reemplazar los VarT en los tipos por los BoundForAll, pero voy a tener 2 posibilidades
  1- El tipo es un ForAllT Ty, en donde los VarT que hay no son los mismo que en la expresión
  2- El tipo no es un ForAllT Ty y los VarT depende de la expresión

Para el segundo caso la idea es muy simple, se recorre el tipo y se cambian los VarT por los BoundForAll donde el Int es la ultima 
posición del 'VarT' en una lista (Mas abajo se explica porque la ultima posición y no la primera)

Para el primer caso es mas complicado, primero se busca y se arma un lista con todos los VarT que aparezcan (sin repetir) y a su vez se
cuenta la cantidad de ForAllT Ty que había en la tipo. Si no coincide hay una variable sin cuantificar, si coincide se procede de la misma 
forma que en el segundo caso.
-}
conversionType :: Type -> [String] -> Type
conversionType (ForAllT (Ty t)) cuan = let (s, i) = conversionForAll [] (ForAllT (Ty t))
                                       in case length s of 
                                            i -> conversionType' (ForAllT (Ty t)) s
                                            _ -> error "Variable no cuantificada"
conversionType t cuan = conversionType' t cuan

{-
Aca es donde se hace el cambio de VarT a BoundForAll propiamente dicho. Hay que tener en cuenta que se puede tener una expresión del 
tipo (Algo sin ForAllT Ty) -> (Algo con ForAllT Ty).
Por esto hay que separa el caso del ForAllT Ty, asi busca los VarT correspondientes en la segunda expresión (que son propias de dicha 
expresión).
-}
conversionType' :: Type -> [String] -> Type
conversionType' (ForAllT (Ty t))  cuan = case cuan of 
                                          [] -> conversionType (ForAllT (Ty t)) cuan
                                          _  -> ForAllT (Ty (conversionType' t cuan))
conversionType' (VarT typee) cuan = BoundForAll (elemIndex' typee cuan)
conversionType' (FunT t1 t2) cuan = FunT (conversionType' t1 cuan) (conversionType' t2 cuan)
conversionType' (ListT t)    cuan = ListT (conversionType' t cuan)
conversionType' t            cuan = t

{-
Esta función se encarga de buscar los VarT que aparecen en el Type, y cuenta la cantidad de veces que parecen los ForAllT Ty.
Se devuelve un tupla con los VarT encontrados (sin repetición) y un numero que cuente la cantidad de ForAllT Ty que había 
(La cantidad de VarT encontrados debe coincidir con el numero de ForAllT)
-}
conversionForAll :: [String] -> Type -> ([String], Int)
conversionForAll cuan (ForAllT (Ty t1)) = let (s, i) = conversionForAll cuan t1
                                          in (s, i+1)
conversionForAll cuan (FunT t1 t2) = let (xs, i)  = conversionForAll cuan t1 
                                         (ys, i') = conversionForAll cuan t2
                                         l = foldl (\zs x -> if x `elem` zs then zs else zs ++ [x]) xs ys -- Elimino VarT repetidos
                                     in (l, i+i')
conversionForAll cuan (VarT typee) = ([typee], 0)
conversionForAll cuan t            = ([], 0)

elemIndex' :: String -> [String] -> Int
elemIndex' n c = fromMaybe (error "La variable no esta cuantificada") (lastElemIndex n c)

{-
Antes elemIndex' era:
elemIndex' n c = fromMaybe (error "La variable no esta cuantificada") (elemIndex n c)

El problema que surge es que como el Sistema F es un polimorfismo paramétrico, los 'para todos' pueden ocurrir en cualquier lugar, 
entonces se puede escribir algo de este tipo:
/\X. \x:X. /\X. \y:X. t

Que baja nuestra definición de Sistema F, los dos '/\X.' son distintos, entonces para dar el correcto BoundForAll tenemos que buscar 
la ultima ocurrencia de 'X' en la lista de los cuantificadores (cuant). Por eso a diferencia de var, busco la ultima ocurrencia.
Pero si se escribiese:
/\X. \x:X. /\Y. \y:Y. t
No se tendría el problema anterior por ser claramente distintos los '/\X.' y '/\Y.'
-}

lastElemIndex :: Eq a => a -> [a] -> Maybe Int
lastElemIndex x xs = case elemIndices x xs of
                       [] -> Nothing
                       l  -> Just (last l)

---------------------------------
-- Sustituye una variable por un término en otro
sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
                  | otherwise = Bound j
sub _ _ (Free n)              = Free n
sub i t (u :@: v)             = sub i t u :@: sub i t v
sub i t (Lam t' u)            = Lam t' (sub (i + 1) t u)

-- Sistema F
sub i t (ForAll u) = ForAll (sub i t u)
sub i t (TApp u v) = TApp (sub i t u) v

-- Bool
sub i t F = F
sub i t T = T
sub i t (IfThenElse t1 t2 t3) = let t1' = sub i t t1
                                    t2' = sub i t t2
                                    t3' = sub i t t3
                                in IfThenElse t1' t2' t3'

-- Nat
sub i t Zero        = Zero
sub i t (Suc u)     = Suc $ sub i t u
sub i t (Rec u v w) = let u' = sub i t u
                          v' = sub i t v
                          w' = sub i t w
                      in Rec u' v' w'

-- List
sub i t Nil          = Nil
sub i t (Cons x xs)  = Cons (sub i t x) (sub i t xs)
sub i t (RecL u v w) = let u' = sub i t u
                           v' = sub i t v
                           w' = sub i t w
                       in RecL u' v' w'

-- Sustituye una variable de tipo por un tipo en concreto (la idea es hacer lo que estipula la regla E-TAppAbs)
sus :: Term -> Type -> Term
sus (Lam t u) typee       = Lam (susType t typee False) (sus u typee)
sus (t1 :@: t2) typee     = sus t1 typee :@: sus t2 typee

sus (ForAll t) typee      = ForAll (sus t typee)
sus (TApp t typee') typee = TApp (sus t typee) typee'

sus (Rec  t u v) typee    = Rec t (sus u typee) v
sus (RecL t u v) typee    = RecL (sus t typee) (sus u typee) (sus v typee)

sus t _                   = t

{-
Esta funcion se encarga de reemplazar los BoundForAll por el tipo correspondiente.

Ademas de usarse en la funcion sus, se utiliza en la funcion infer'. Pero hay una diferencia, en sus se debe ignorar el caso ForAllT Ty, 
mientras que en infer no se debe ignorar este caso (esto es debido a la forma en la ques se manejan los BoundForAll dentro de los 
ForAll y ForAllT Ty). Para marcar esta difernecia se usa un Bool, si es True es el caso del infer', si es False es el caso del sus.

-}
susType :: Type -> Type -> Bool -> Type
susType (FunT t1 t2) typee b     = FunT (susType t1 typee b) (susType t2 typee b)
susType (ListT t)    typee b     = ListT (susType t typee b)
susType (ForAllT (Ty t))  typee True  = ForAllT (Ty (susType t typee True))
susType (BoundForAll k) typee _  = if k == 0 then typee else BoundForAll (k - 1)
susType t _                   _  = t

-- Convierte valor a un término equivalente
quote :: Value -> Term
quote (VLam t f) = Lam t f

-- Sistema F
quote (VForAll t) = ForAll t

-- Bool
quote (VBool NTrue)  = T
quote (VBool NFalse) = F

-- Nat
quote (VNum NZero)    = Zero
quote (VNum (NSuc n)) = Suc $ quote $ VNum n

-- List
quote (VList VNil) = Nil
quote (VList (VCons x xs)) = Cons (quote x) (quote (VList xs))

-- Evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value
eval nvs (Free n)    = fst $ fromJust (lookup n nvs)
eval nvs (Lam t u)   = VLam t u
eval nvs (t1 :@: t2) = let (VLam _ t1') = eval nvs t1
                           t2' = eval nvs t2
                       in eval nvs $ sub 0 (quote t2') t1'

-- Sistema F
eval nvs (ForAll t)     = VForAll t
eval nvs (TApp t typee) = let t' = eval nvs t
                          in case t' of
                               VForAll u -> eval nvs (sus u typee)
                               _         -> error $ "El termino dentro de la aplicación " ++ show t' ++ " no evalúa a un VForAll"

-- Bool
eval nvs T = VBool NTrue
eval nvs F = VBool NFalse
eval nvs (IfThenElse t1 t2 t3) = case eval nvs t1 of 
                                   VBool NTrue -> eval nvs t2
                                   VBool NFalse -> eval nvs t3
                                   val -> error $ "El termino " ++ show val ++ " no evalúa a un BoolVal"

-- Nat
eval nvs Zero    = VNum NZero
eval nvs (Suc n) = let (VNum n') = eval nvs n
                   in VNum $ NSuc n'
eval nvs (Rec t1 t2 t3) = case eval nvs t3 of
                            VNum NZero -> eval nvs t1
                            VNum (NSuc t) ->  let t' = quote $ VNum t
                                              in eval nvs $ t2 :@: Rec t1 t2 t' :@: t'
                            val -> error $ "Se esperaba un NumVal pero se recibió " ++ show val

-- Lista
eval nvs Nil         = VList VNil
eval nvs (Cons x xs) = let x' = eval nvs x
                           (VList xs') = eval nvs xs
                       in VList $ VCons x' xs'
eval nvs (RecL t1 t2 t3) = case eval nvs t3 of
                             VList VNil -> eval nvs t1
                             VList (VCons n lv) -> let n'  = quote $ n
                                                       lv' = quote $ VList lv 
                                                   in eval nvs $ t2 :@: n' :@: lv' :@: RecL t1 t2 lv'
                             val -> error $ "Se esperaba un ListVal pero se recibió " ++ show val

-- Expresión incorrecta
eval _ t = error $ "No se puede convertir el termino " ++ show t ++ " a un valor"

---------------------------------
-- Infiere el tipo de un término
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- funciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

-- Imprime que el Type no es función
notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

-- Imprime que la variable no esta definida
notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

-- Imprime que los Type no coinciden
matchError :: Type -> Type -> Either String Type
matchError t1 t2 = err $ "se esperaba " ++ render (printType t1) ++ ", pero " ++ render (printType t2) ++ " fue inferido."

-- Recibe un Type y un error o Type, si es el error lo devuelve, si no se fija que los Type coincidan
match :: Type -> Either String Type -> Either String Type
match expected_type e@(Left _) = e
match expected_type e@(Right t) | expected_type == t = e
                                | isList expected_type && t == ListTEmpty = Right expected_type
                                | otherwise = matchError expected_type t
  where
    isList (ListT _) = True
    isList _         = False

-- Chequea que el Type sea una función
checkIsFun :: Either String Type -> Either String Type
checkIsFun e@(Left _)  = e
checkIsFun e@(Right t) = case t of
                           FunT t1 t2 -> e
                           _ -> notfunError t

-- Chequea que el Type sea una función usada en la recursion de lista
checkIsFunInRL :: Either String Type -> Either String Type
checkIsFunInRL e@(Left _)  = e
checkIsFunInRL e@(Right t) = case t of
                               FunT u (FunT (ListT u') (FunT (ListT v) (ListT v'))) -> 
                                          if u == u' && v == v' then e else err "El tipo de la función en RL esta mal"
                               _ -> err "No es el tipo esperados para la operación RL"

-- Dado un tupla y un Type, se fija que la primer componente coincida con el Type
-- De hacerlo devuelve la segunda componente, sino devuelve un error.
singleMatch :: (Type, Either String Type) -> Either String Type -> Either String Type
singleMatch _ e@(Left _) = e
singleMatch (expected_type, rst) e@(Right t) | t == expected_type = rst 
                                             | otherwise = matchError expected_type t

---------------------------------

infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _  (Bound i) = ret (c !! i)
infer' _  e (Free  n) = maybe (notfoundError n) (ret . snd) (lookup n e)
infer' c e (t :@: u)  = checkIsFun (infer' c e t) >>= \(FunT t1 t2) -> match t1 (infer' c e u) >> ret t2
infer' c e (Lam t u)  = infer' (t : c) e u >>= \tu -> ret $ FunT t tu

-- Sistema F
infer' c e (ForAll t)              = infer' c e t >>= \t' -> ret $ ForAllT (Lambd t')
infer' c e (TApp (ForAll t) typee) = infer' c e (sus t typee)
infer' c e (TApp t typee)          = infer' c e t >>= \t' ->
                                              case t' of
                                                ForAllT (Ty u) -> ret $ susType u typee True
                                                _ -> err "Aplicación a un termino no polimorfico"

-- Bool
infer' c e T = ret BoolT
infer' c e F = ret BoolT
infer' c e (IfThenElse t1 t2 t3) = 
  infer' c e t2 >>= \tt2 ->
    singleMatch (BoolT, match tt2 (infer' c e t3)) (infer' c e t1) >> ret tt2 
                                                                            
-- Nat
infer' c e Zero    = ret NatT
infer' c e (Suc t) = match NatT $ infer' c e t
infer' c e (Rec t1 t2 t3) = 
  infer' c e t1 >>= \tt1 ->
    singleMatch (FunT tt1 (FunT NatT tt1), match NatT (infer' c e t3)) (infer' c e t2) >> ret tt1

-- List
infer' c e Nil           = ret ListTEmpty
infer' c e (Cons t1 Nil) = infer' c e t1 >>= \tt1 -> ret (ListT tt1)
infer' c e (Cons t1 t2)  = infer' c e t1 >>= \tt1 -> match (ListT tt1) (infer' c e t2)
infer' c e (RecL t1 t2 t3) = 
  infer' c e t1 >>= \tt1 -> infer' c e t3 >>= \tt3 -> 
    case tt1 of
      ListTEmpty -> checkIsFunInRL (infer' c e t2) >>= \(FunT t (FunT t' (FunT v v'))) -> match t' (ret tt3) >> ret v    
      _ -> case tt3 of
              ListT t -> singleMatch (FunT t (FunT tt3 (FunT tt1 tt1)), ret tt3) (infer' c e t2) >> ret tt1
