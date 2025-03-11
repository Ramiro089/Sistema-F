module SystemF ( conversion, eval, infer, quote )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=), (>>) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-- Convierte un LamTerm a un Term, aplicando una funcion de conversion
toTerm:: (LamTerm -> Term) -> LamTerm -> [String] -> Term
toTerm f (LAbs name typee t) c = Lam (conversionFunT typee (reverse c)) $ f t
toTerm f (LApp t1 t2) _        = f t1 :@: f t2

-- Sistema F
toTerm f (LTAbs name t) _  = ForAll (f t)
toTerm f (LTApp t typee) c = TApp (f t) (conversionFunT typee (reverse c)) 

-- Bool
toTerm f LTrue _ = T
toTerm f LFalse _= F
toTerm f (LIfThenElse t1 t2 t3) _ = IfThenElse (f t1) (f t2) (f t3)

-- Nat
toTerm f LZero _           = Zero
toTerm f (LSuc t) _        = Suc $ f t
toTerm f (LRec t1 t2 t3) _ = Rec (f t1) (f t2) (f t3)

-- List
toTerm f LNil _ = Nil
toTerm f (LCons t1 t2) _    = Cons (f t1) (f t2)
toTerm f (LRecL t1 t2 t3) _ = RecL (f t1) (f t2) (f t3)

toTerm f t _ = error $ "No se puede convertir el lambda termino " ++ show t ++ " a un termino"

-- conversion a Term
conversion :: LamTerm -> Term
conversion = conversion' [] []

conversion' :: [String] -> [String] -> LamTerm -> Term
conversion' vars cuan (LVar name)                 = maybe (Free (Global name)) Bound (elemIndex name vars)
conversion' vars cuan (LAbs name (VarT typee) t') = conversion' vars cuan (LAbs name (BoundForAll (elemIndex' typee cuan)) t')
conversion' vars cuan t@(LAbs name _ _)           = toTerm (conversion' (name:vars) cuan) t cuan
conversion' vars cuan t@(LTAbs name lamTerm)      = toTerm (conversion' vars (cuan ++ [name])) t cuan
conversion' vars cuan t                           = toTerm (conversion' vars cuan) t cuan

---------------------------------
-- La idea de esta función es que cambie las abstracciones que están en los tipo
conversionFunT :: Type -> [String] -> Type
conversionFunT (VarT typee) cuan = (BoundForAll (elemIndex' typee cuan))
conversionFunT (FunT t1 t2) cuan = FunT (conversionFunT t1 cuan) (conversionFunT t2 cuan)
conversionFunT (ListT t1) cuan   = ListT (conversionFunT t1 cuan)
conversionFunT (ForAllT t1) cuan = ForAllT (conversionFunT t1 cuan)
conversionFunT t cuan = t

elemIndex' :: String -> [String] -> Int
elemIndex' n c = case (elemIndex n c) of
                        Just m -> m
                        Nothing -> 0

---------------------------------

-- substituye una variable por un término en otro término
sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
                  | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)

-- Bool
sub i t F = F
sub i t T = T
sub i t (IfThenElse t1 t2 t3) = let t1' = sub i t t1
                                    t2' = sub i t t2
                                    t3' = sub i t t3
                                in IfThenElse t1' t2' t3'

-- Nat
sub i t Zero = Zero
sub i t (Suc u) = Suc $ sub i t u
sub i t (Rec u v w) = let u' = sub i t u
                          v' = sub i t v
                          w' = sub i t w
                      in Rec u' v' w'


sub i t Nil = Nil
sub i t (Cons x xs) = Cons (sub i t x) (sub i t xs)
sub i t (RecL u v w) = let u' = sub i t u
                           v' = sub i t v
                           w' = sub i t w
                       in RecL u' v' w'

-- Sustituye una variable de tipo por un tipo en concreto
sus :: Term -> Type -> Term
sus (Lam t u) typee       = Lam (susTipo t typee) (sus u typee)
sus (t1 :@: t2) typee     = sus t1 typee :@: sus t2 typee
sus (ForAll t) typee      = ForAll (sus t typee)
sus (TApp t typee') typee = TApp (sus t typee) typee'
sus (RecL u v w) typee    = RecL (sus u typee) (sus v typee) (sus w typee)
sus t _                   = t

-- Sustitución de tipos en tipos
susTipo :: Type -> Type -> Type
susTipo (FunT t1 t2) typee    = FunT (susTipo t1 typee) (susTipo t2 typee)
susTipo (ListT t1) typee      = ListT (susTipo t1 typee)
susTipo (BoundForAll k) typee = if k == 0 then typee else BoundForAll (k - 1)
susTipo t _                   = t

-- convierte un valor en el término equivalente
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

-- evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value
eval nvs (Free n)    = fst $ fromJust $ lookup n nvs
eval nvs (Lam t u)   = VLam t u
eval nvs (t1 :@: t2) = let (VLam _ t1') = eval nvs t1
                           t2' = eval nvs t2
                       in eval nvs $ sub 0 (quote t2') t1'

-- Sistema F
eval nvs (ForAll t) = VForAll t
eval nvs (TApp (ForAll t) typee) = eval nvs (sus t typee) 
eval nvs (TApp (Free n) typee)   = eval nvs (TApp (quote $ fst $ fromJust $ lookup n nvs) typee)
eval nvs (TApp t typee)          = let t' = eval nvs t
                                   in eval nvs (TApp (quote t') typee)

-- Bool
eval nvs T = VBool NTrue
eval nvs F = VBool NFalse
eval nvs (IfThenElse T t2 t3)  = eval nvs t2
eval nvs (IfThenElse F t2 t3)  = eval nvs t3
eval nvs (IfThenElse t1 t2 t3) = case (eval nvs t1) of 
                                   VBool NTrue -> eval nvs t2
                                   VBool NFalse -> eval nvs t3
                                   val -> error $ "El termino " ++ show val ++ " no evalúa a un BoolVal"

-- Nat
eval nvs Zero = VNum NZero
eval nvs (Suc n) = let (VNum n') = eval nvs n
                   in VNum $ NSuc n'
eval nvs (Rec t1 t2 t3) = case eval nvs t3 of
                            VNum NZero -> eval nvs t1
                            VNum (NSuc t) ->  let t' = quote $ VNum t
                                              in eval nvs $ t2 :@: Rec t1 t2 t' :@: t'
                            val -> error $ "Se esperaba un NumVal pero se recibió " ++ show val

-- Lista
eval nvs Nil = VList VNil
eval nvs (Cons x xs) = let x' = eval nvs x
                           (VList xs') = eval nvs xs
                       in VList $ VCons x' xs'

eval nvs (RecL t1 t2 t3) = case eval nvs t3 of
                             VList VNil -> eval nvs t1
                             VList (VCons n lv) -> let n'  = quote $ n
                                                       lv' = quote $ VList lv 
                                                   in eval nvs $ t2 :@: n' :@: lv' :@: RecL t1 t2 lv'
                             val -> error $ "Se esperaba un ListVal pero se recibió " ++ show val

eval _ t = error $ "No se puede convertir el termino " ++ show t ++ " a un valor"

---------------------------------

-- infiere el tipo de un término
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []
  where xs = [ c : n | n <- "" : map show [(1 :: Integer) ..], c <- ['X', 'Y', 'Z'] ++ ['A' .. 'W']]

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=) :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v

matchError :: Type -> Type -> Either String Type
matchError t1 t2 = err $  "se esperaba " ++ render (printType t1) ++ ", pero " ++ render (printType t2) ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."


match :: Type -> Either String Type -> Either String Type
match expected_type e@(Left _) = e
match expected_type e@(Right t) | expected_type == t = e
                                | t == (ListTEmpty) = e
                                | otherwise = matchError expected_type t

checkIsFun :: Either String Type -> Either String Type
checkIsFun e@(Left _) = e
checkIsFun e@(Right t) = case t of
                           FunT t1 t2 -> e
                           _ -> notfunError t

(>>) :: Either String Type -> Either String Type -> Either String Type
(>>) v f = v >>= const f

matchMultiple :: [(Type, Either String Type)] -> Either String Type -> Either String Type
matchMultiple _ e@(Left _) = e
matchMultiple t1s e@(Right t) = fromMaybe (matchMultipleError t1s t) (lookup t t1s)
  where
    matchMultipleError t1s t2 =
      err  $ "se esperaba " ++ intercalate " o " (map (render . printType . fst) t1s) ++ ", pero " ++ render (printType t2) ++ " fue inferido."

-- infiere el tipo de un término
infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _  (Bound i)  = ret (c !! i)
infer' _  e (Free  n)  = maybe (notfoundError n) (ret . snd) (lookup n e)
infer' c e (t :@: u) = checkIsFun (infer' c e t) >>= \(FunT t1 t2) -> match t1 (infer' c e u) >> ret t2
infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu

-- Sistema F
infer' c e (ForAll t)              = infer' c e t >>= \t' -> ret $ ForAllT t'
infer' c e (TApp (ForAll t) typee) = infer' c e (sus t typee)
infer' c e (TApp (Free n) typee)   = infer' c e (TApp (quote $ fst $ fromJust $ (lookup n e)) typee)
infer' c e (TApp t typee)          = infer' c e t >>= \t' ->
                                              case t' of
                                                ForAllT u -> ret $ susTipo u typee
                                                _ -> error $ "Aplicación a un termino no polimorfico"

-- Bool
infer' c e T = ret BoolT
infer' c e F = ret BoolT
infer' c e (IfThenElse t1 t2 t3) = 
  infer' c e t2 >>= \tt2 ->
    matchMultiple [
      (BoolT, match tt2 (infer' c e t3))
    ] (infer' c e t1) 
    >> ret tt2 
                                                                            
-- Nat
infer' c e Zero    = ret NatT
infer' c e (Suc t) = match NatT $ infer' c e t
infer' c e (Rec t1 t2 t3) = 
  infer' c e t1 >>= \tt1 ->
    matchMultiple [
      (FunT tt1 (FunT NatT tt1), match NatT (infer' c e t3))
    ] (infer' c e t2) 
    >> ret tt1

-- List
infer' c e Nil           = ret (ListTEmpty)
infer' c e (Cons t1 Nil) = infer' c e t1 >>= \tt1 -> ret (ListT tt1)
infer' c e (Cons t1 t2)  = infer' c e t1 >>= \tt1 -> match (ListT tt1) (infer' c e t2)

infer' c e (RecL t1 t2 t3) = 
  infer' c e t1 >>= \tt1 -> (infer' c e t3 >>= \tt3 -> 
                                case tt3 of
                                  ListT t -> matchMultiple [
                                               (FunT t (FunT tt3 (FunT tt1 tt1)), ret tt3)
                                             ] (infer' c e t2) 
                                             >> ret tt1)