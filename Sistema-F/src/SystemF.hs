{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}    -- En algunos caos de los Let me interesa un solo caso, estos para evitar el Warning de los casos faltantes
module SystemF ( conversion, eval, infer, quote )
where

import           Data.List                  ( elemIndex, elemIndices )
import           Data.Maybe                 ( fromJust, fromMaybe, maybe )
import           Prelude
import           Text.PrettyPrint.HughesPJ  ( render )
import           PrettyPrinter
import           Common


-- Convierte un LamTerm a un Term, aplicando una función de conversión
toTerm:: (LamTerm -> Term) -> LamTerm -> [String] -> Term
toTerm f (LAbs _ typee t) c = Lam (conversionType (reverse c) typee) (f t)
toTerm f (LApp t1 t2) _     = App (f t1) (f t2)

-- Sistema F
toTerm f (LTAbs _ t)  _    = ForAll (f t)
toTerm f (LTApp t typee) c = TApp (f t) (conversionType (reverse c) typee)

-- Bool
toTerm f LTrue  _ = T
toTerm f LFalse _ = F
toTerm f (LIfThenElse t1 t2 t3) _ = IfThenElse (f t1) (f t2) (f t3)

-- Nat
toTerm f LZero _           = Zero
toTerm f (LSuc t) _        = Suc (f t)
toTerm f (LRec t1 t2 t3) _ = Rec (f t1) (f t2) (f t3)

-- List
toTerm f LNil _             = Nil
toTerm f (LCons t1 t2) _    = Cons (f t1) (f t2)
toTerm f (LRecL t1 t2 t3) _ = RecL (f t1) (f t2) (f t3)

toTerm f t _ = error $ "No se puede convertir el lambda termino " ++ show t ++ " a un termino"

-- | Convierte un termino en formato LamTerm a uno en formato Term
conversion :: LamTerm -> Term
conversion = conversion' [] []

conversion' :: [String] -> [String] -> LamTerm -> Term
conversion' vars cuan (LVar name)       = maybe (FreeGlobal name) Bound (elemIndex name vars)
conversion' vars cuan t@(LAbs name _ _) = toTerm (conversion' (name:vars) cuan) t cuan
conversion' vars cuan t@(LTAbs name _)  = toTerm (conversion' vars (name:cuan)) t cuan
conversion' vars cuan t                 = toTerm (conversion' vars cuan) t cuan

------------------------------------------

-- Transforma el Type que recibe a type valido
conversionType :: [String] -> Type -> Type
conversionType = conversionType' [] 

conversionType' :: [String] -> [String] -> Type -> Type
conversionType' cuan cuanOG (VarT typee)         = BoundForAll $ maybe (External (elemIndex' typee cuanOG)) Inner (lastElemIndex typee cuan)
conversionType' cuan cuanOG t@(ForAllT (Lt s _)) = toType (conversionType' (cuan ++ [s]) cuanOG) t
conversionType' cuan cuanOG t                    = toType (conversionType' cuan cuanOG) t

toType :: (Type -> Type) -> Type -> Type
toType f (ForAllT (Lt s u)) = ForAllT (Ty (f u))
toType f (FunT t1 t2)       = FunT  (f t1) (f t2)
toType f (ListT t)          = ListT (f t)
toType f t                  = t

------------------------------------------

elemIndex' :: String -> [String] -> Int
elemIndex' n c = fromMaybe (error "Hay variables que no esta cuantificadas") (lastElemIndex n c)

lastElemIndex :: Eq a => a -> [a] -> Maybe Int
lastElemIndex x xs = case elemIndices x xs of
                       [] -> Nothing
                       l  -> Just (last l) 
{-
Antes elemIndex' era:
elemIndex' n c = fromMaybe (error "La variable no esta cuantificada") (elemIndex n c)

El problema que surge es que como el Sistema F es un polimorfismo paramétrico, los 'para todos' pueden ocurrir en cualquier lugar, 
entonces se puede escribir algo de este tipo:
/\X. \x:X. /\X. \y:X. t

Que baja nuestra definición de Sistema F, los dos '/\X.' son distintos, entonces para dar el correcto BoundForAll tenemos que buscar 
la ultima ocurrencia de 'X' en la lista de la lista cuantOG.

Este mismo problema puede ocurrir cuando se tiene que x tiene tipo (\/X. X -> \/X. X -> X), aca se hace lo mismo se cambia para que quede 
(\/X. X -> \/ Y. Y -> Y), en este caso es la ultima ocurrencia de la lista cuan
-}

------------------------------------------
-- Sustituye una variable por un termino en otro
sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
                  | otherwise = Bound j
sub _ _ (FreeGlobal n)        = FreeGlobal n
sub i t (App u v)             = App (sub i t u) (sub i t v)
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
sub i t (Suc u)     = Suc (sub i t u)
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

-- Sustituye una variable de tipo por un tipo en concreto (la idea es hacer la regla E-TAppAbs)
sus :: Term -> Type -> Term
sus (Lam t u) typee       = Lam (susType t typee False) (sus u typee)
sus (App t1 t2) typee     = App (sus t1 typee) (sus t2 typee)

-- Sistema F
sus (ForAll t) typee      = ForAll (sus t typee)
sus (TApp t typee') typee = TApp (sus t typee) typee'

-- Bool
sus (IfThenElse t1 t2 t3) typee = IfThenElse (sus t1 typee) (sus t2 typee) (sus t3 typee) 

-- Nat
sus (Suc t) typee      = Suc (sus t typee)
sus (Rec  t u v) typee = Rec t (sus u typee) v

-- List
sus (RecL t u v) typee = RecL (sus t typee) (sus u typee) (sus v typee)
sus (Cons t1 t2) typee = Cons (sus t1 typee) (sus t2 typee)

-- Cualquier Otro
sus t _                = t

------------------------------------------
{-
Esta función se encarga de reemplazar los (BoundForAll Pos) por el tipo correspondiente.
Se utiliza en la función sus y en la función infer. Pero hay una diferencia, en sus no se debe entrar al caso de BoundForAll (Inner _ ),
en infer si se debe. Para esto se utiliza un Bool, que indica el caso.
-}
susType :: Type -> Type -> Bool -> Type
susType (FunT t1 t2)        typee b = FunT (susType t1 typee b) (susType t2 typee b)
susType (ListT t)           typee b = ListT (susType t typee b)
susType (ForAllT (Ty t))    typee b = ForAllT (Ty (susType t typee b))
susType (ForAllT (Lambd t)) typee b = ForAllT (Lambd (susType t typee b))
susType (BoundForAll (External k)) typee _ = if k == 0 then typee else BoundForAll $ External (k - 1)
susType (BoundForAll (Inner k)) typee True = if k == 0 then typee else BoundForAll $ Inner (k - 1)
susType t _ _                              = t

-- | Convierte valor a un termino (de tipo Term) equivalente
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
quote (VList VNil)         = Nil
quote (VList (VCons x xs)) = Cons (quote x) (quote (VList xs))

-- | Evalúa un termino (de tipo Term) en un entorno dado
eval :: NameEnv Value Type -> Term -> Value
eval nvs (FreeGlobal n) = fst $ fromJust (lookup n nvs)
eval nvs (Lam t u)      = VLam t u
eval nvs (App t1 t2)    = let (VLam _ t1') = eval nvs t1
                              t2' = eval nvs t2
                          in eval nvs $ sub 0 (quote t2') t1'

-- Sistema F
eval nvs (ForAll t)     = VForAll t
eval nvs (TApp t typee) = let t' = eval nvs t
                          in case t' of
                               VForAll u -> eval nvs (sus u typee)
                               _         -> error $ "El termino dentro de la aplicacion " ++ show t' ++ " no evalua a un VForAll"

-- Bool
eval nvs T = VBool NTrue
eval nvs F = VBool NFalse
eval nvs (IfThenElse t1 t2 t3) = case eval nvs t1 of
                                   VBool NTrue  -> eval nvs t2
                                   VBool NFalse -> eval nvs t3
                                   val          -> error $ "El termino " ++ show val ++ " no evalua a un BoolVal"

-- Nat
eval nvs Zero    = VNum NZero
eval nvs (Suc n) = let (VNum n') = eval nvs n
                   in VNum (NSuc n')
eval nvs (Rec t1 t2 t3) = case eval nvs t3 of
                            VNum NZero    -> eval nvs t1
                            VNum (NSuc t) ->  let t' = quote $ VNum t
                                              in eval nvs $ App (App t2 (Rec t1 t2 t')) t'
                            val           -> error $ "Se esperaba un NumVal pero se recibio " ++ show val

-- Lista
eval nvs Nil         = VList VNil
eval nvs (Cons x xs) = let x'          = eval nvs x
                           (VList xs') = eval nvs xs
                       in VList (VCons x' xs')
eval nvs (RecL t1 t2 t3) = case eval nvs t3 of
                             VList VNil         -> eval nvs t1
                             VList (VCons n lv) -> let n'  = quote n
                                                       lv' = quote (VList lv)
                                                   in eval nvs $ App (App (App t2 n') lv') (RecL t1 t2 lv')
                             val                -> error $ "Se esperaba un ListVal pero se recibio " ++ show val

-- Expresión incorrecta
eval _ t = error $ "No se puede convertir el termino " ++ show t ++ " a un valor"

------------------------------------------
-- | Infiere el tipo de un término (de tipo Term)
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- funciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

-- Imprime que el tipo no es función
notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

-- Imprime que la variable no esta definida
notfoundError :: String -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

-- Imprime que los tipo no coinciden
matchError :: Type -> Type -> Either String Type
matchError t1 t2 = err $ "se esperaba " ++ t1' ++ ", pero " ++ t2' ++ " fue inferido."
  where t1' = render (printType t1)
        t2' = render (printType t2)

-- Recibe un tipo y un error o tipo, si es el error lo devuelve, si no se fija que los tipo coincidan
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
                           _          -> notfunError t

-- Chequea que el tipo sea una función usada en la recursion de lista
checkIsFunInRL :: Either String Type -> Either String Type
checkIsFunInRL e@(Left _)  = e
checkIsFunInRL e@(Right t) = case t of
                               FunT u (FunT (ListT u') (FunT (ListT v) (ListT v'))) ->
                                          if u == u' && v == v' then e else err "El tipo de la funcion en RL no es correcto"
                               _ -> err "No es el tipo esperados para la operación RL"

-- Dado un tupla y un tipo, se fija que la primer componente coincida con el tipo
-- De hacerlo devuelve la segunda componente, sino devuelve un error.
singleMatch :: (Type, Either String Type) -> Either String Type -> Either String Type
singleMatch _ e@(Left _) = e
singleMatch (expected_type, rst) e@(Right t) | t == expected_type = rst
                                             | otherwise = matchError expected_type t

------------------------------------------

infer' :: [Type] -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i)      = ret (c !! i)
infer' _ e (FreeGlobal n) = maybe (notfoundError n) (ret . snd) (lookup n e)
infer' c e (App t u)      = checkIsFun (infer' c e t) >>= \(FunT t1 t2) -> match t1 (infer' c e u) >> ret t2
infer' c e (Lam t u)      = infer' (t : c) e u >>= \u' -> ret $ FunT t u'

-- Sistema F
infer' c e (ForAll t)              = infer' c e t >>= \t' -> ret $ ForAllT (Lambd t')
infer' c e (TApp (ForAll t) typee) = infer' c e (sus t typee)
infer' c e (TApp t typee)          = infer' c e t >>= \t' ->
                                              case t' of
                                                ForAllT (Ty u)    -> ret $ susType u typee True
                                                ForAllT (Lambd u) -> ret $ susType u typee False
                                                _                 -> err $ "Esta expresion " ++ show t ++ " no esta cuantificada" 

-- Bool
infer' c e T = ret BoolT
infer' c e F = ret BoolT
infer' c e (IfThenElse t1 t2 t3) =
  infer' c e t2 >>= \t2' ->
    singleMatch (BoolT, match t2' (infer' c e t3)) (infer' c e t1) >> ret t2'

-- Nat
infer' c e Zero    = ret NatT
infer' c e (Suc t) = match NatT $ infer' c e t
infer' c e (Rec t1 t2 t3) =
  infer' c e t1 >>= \t1' ->
    singleMatch (FunT t1' (FunT NatT t1'), match NatT (infer' c e t3)) (infer' c e t2) >> ret t1'

-- List
infer' c e Nil             = ret ListTEmpty
infer' c e (Cons t1 t2)    = infer' c e t1 >>= \t1' -> match (ListT t1') (infer' c e t2)
infer' c e (RecL t1 t2 t3) =
  infer' c e t1 >>= \t1' -> infer' c e t3 >>= \t3' ->
    case t1' of
      ListTEmpty -> checkIsFunInRL (infer' c e t2) >>= \(FunT t (FunT t' (FunT v v'))) -> match t' (ret t3') >> ret v
      _          -> case t3' of
                       ListT t -> singleMatch (FunT t (FunT t3' (FunT t1' t1')), ret t3') (infer' c e t2) >> ret t1'
                       _       -> err $ "El tercer argumento de RL, " ++ show t3 ++ " no es un ListT"
