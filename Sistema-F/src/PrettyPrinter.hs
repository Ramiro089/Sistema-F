module PrettyPrinter ( printTerm, printType )
where

import  Common
import  Text.PrettyPrint.HughesPJ
import  Prelude hiding ((<>))
import Data.String (String)


-- Lista de posibles cuantificadores
cuantificadores :: [String]
cuantificadores = 
  [ c : n
  | n <- "" : map show [(1 :: Integer) ..]
  , c <- ['X', 'Y', 'Z'] ++ ['A' .. 'W']
  ]

-- Lista de posibles nombres para variables
vars :: [String]
vars =
  [ c : n
  | n <- "" : map show [(1 :: Integer) ..]
  , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
  ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-------------------------------------------------
-- pretty-printer términos

pp :: Int -> [String] -> Int -> [String] -> Term -> Doc
pp i v _ _ (Bound k) = text (v !! (i - k - 1))
pp _  _   k cuanExter (Free (Global s)) = text s
pp i v k cuanExter (t :@: u) = 
  sep [parensIf (isLam t) (pp i v k cuanExter t), nest 1 (parensIf (isLam u || isApp u) (pp i v k cuanExter u))]

pp i v k cuanExter (Lam t c) =
  text "\\"
    <> text (v !! i)
    <> text ":"
    <> printType t   -- Ver esto
    <> text ". "
    <> pp (i+1) v k cuanExter c

pp i v k cuanExter (ForAll term) = 
  text "/\\"
    <> text (cuanExter !! k)
    <> text ". "
    <> pp i v (k+1) cuanExter  term

pp i v k cuanExter  (TApp t typee) =
  parens (pp i v k cuanExter t)
    <> text " <"
    <> printType typee
    <> text ">"
  
pp i v k cuanExter t | isBool t  = printBool i v k cuanExter t
                     | isNat t   = printNat  i v k cuanExter t
                     | otherwise = printList i v k cuanExter t


applyParen :: Int -> [String] -> Int -> [String] -> Term -> Doc
applyParen i v k cuanExter t = parensIf (not $ isAtom t) (pp i v k cuanExter t)

printBool :: Int -> [String] -> Int -> [String] -> Term -> Doc
printBool i v k cuanExter T = text "true" 
printBool i v k cuanExter F = text "false"
printBool i v k cuanExter (IfThenElse t1 t2 t3) =
  text "if "
    <> pp i v k cuanExter t1
    <> text " then "
    <> pp i v k cuanExter t2
    <> text " else "
    <> pp i v k cuanExter t3

printNat :: Int -> [String] -> Int -> [String] -> Term -> Doc
printNat i v k cuanExter Zero            = text "0"
printNat i v k cuanExter (Suc t@(Suc _)) = sep [text "suc", pp i v k cuanExter t]
printNat i v k cuanExter (Suc t)         = sep [text "suc", applyParen i v k cuanExter t]
printNat i v k cuanExter (Rec t u w)     = sep [text "R", applyParen i v k cuanExter t, applyParen i v k cuanExter u, applyParen i v k cuanExter w]
printNat i v k cuanExter t               = pp i v k cuanExter t

printList :: Int -> [String] -> Int -> [String] -> Term -> Doc
printList i v k cuanExter Nil          = text "nil"
printList i v k cuanExter (Cons t u)   = sep [text "cons", applyParen i v k cuanExter t, applyParen i v k cuanExter u]
printList i v k cuanExter (RecL t u w) = sep [text "RL", applyParen i v k cuanExter t, applyParen i v k cuanExter u, applyParen i v k cuanExter w]
printList i v k cuanExter t            = pp i v k cuanExter t

isLam :: Term -> Bool
isLam (Lam _ _) = True
isLam _         = False

isApp :: Term -> Bool
isApp (_ :@: _) = True
isApp _         = False

isBool :: Term -> Bool
isBool T                  = True
isBool F                  = True
isBool (IfThenElse _ _ _) = True
isBool _                  = False

isNat :: Term -> Bool
isNat Zero        = True
isNat (Suc _)     = True
isNat (Rec _ _ _) = True
isNat _           = False

isAtom :: Term -> Bool
isAtom Zero = True
isAtom Nil  = True
isAtom T    = True
isAtom F    = True
isAtom _    = False

-------------------------------------------------
-- pretty-printer 
printTypeAuxForAll :: Type -> Int -> Int -> [String] -> [String] -> Doc
printTypeAuxForAll (ForAllT (Ty t)) n k cuanInter cuanExter = parens $
  text "\\/ "
    <> text (cuanInter !! k)
    <> text ". "
    <> printTypeAuxForAll t n (k+1) cuanInter cuanExter
printTypeAuxForAll (FunT t1 t2) n k cuanInter cuanExter = sep [parensIf (isFun t1) (printTypeAuxForAll t1 n k cuanInter cuanExter), text "->", printTypeAuxForAll t2 n k cuanInter cuanExter] 
printTypeAuxForAll t n k  cuanInter cuanExter = printTypeAux t n cuanInter cuanExter
    
printTypeAux :: Type -> Int -> [String] -> [String] -> Doc
-- Sistema F
printTypeAux (ForAllT (Lambd t)) n cuanInter cuanExter = parens $
  text "\\/ "
    <> text (cuanExter !! n)
    <> text ". "
    <> printTypeAux t (n+1) cuanInter cuanExter
printTypeAux t@(ForAllT (Ty _)) n cuanInter cuanExter = printTypeAuxForAll t n 0 cuanInter cuanExter
printTypeAux (BoundForAll (Inner k))  _  cuanInter cuanExter = text (cuanInter !! k)
printTypeAux (BoundForAll (External k))  _  cuanInter cuanExter = text (cuanExter !! k)

-------------------------------------------------------------------------------------

-- Bool, Nat, Empty
printTypeAux BoolT  _ _ _ = text "Bool"
printTypeAux NatT   _ _ _ = text "Nat"
printTypeAux EmptyT _ _ _ = text "E"

-- Funcion
printTypeAux (FunT t1 t2) n cuanInter cuanExter = sep [parensIf (isFun t1) (printTypeAux t1 n cuanInter cuanExter), text "->", printTypeAux t2 n cuanInter cuanExter]

-- List
printTypeAux (ListT t)  n cuanInter cuanExter = text "List " <> parensIf (inList t) (printTypeAux t n cuanInter cuanExter)
printTypeAux ListTEmpty _ cuanInter cuanExter = text "Lista Vacía"

printType :: Type -> Doc
printType t = printTypeAux t 0 cuanInter cuanExter
  where cuanInter = map (++ "'") cuantificadores
        cuanExter = cuantificadores

-------------------------------------------------

isFun :: Type -> Bool
isFun (FunT _ _) = True
isFun _          = False

inList :: Type -> Bool
inList (ListT _)        = True
inList (FunT _ _)       = True
inList (ForAllT (Ty _)) = True
inList _                = False

fv :: Term -> [String]
fv (Bound _)         = []
fv (Free (Global n)) = [n]
fv (t :@: u)         = fv t ++ fv u
fv (Lam _ u)         = fv u

-- Sistema F
fv (ForAll t) = fv t
fv (TApp t _) = fv t 

-- Bool
fv T                  = []
fv F                  = []
fv (IfThenElse t u v) = fv t ++ fv u ++ fv v

-- Nat
fv Zero        = []
fv (Suc t)     = fv t
fv (Rec t u v) = fv t ++ fv u ++ fv v

-- List
fv Nil          = []
fv (Cons t u)   = fv t ++ fv u
fv (RecL t u v) = fv t ++ fv u ++ fv v

-------------------------------------------------
printTerm :: Term -> Doc
printTerm t = pp 0 vars' 0 cuanExter t
  where cuanExter = cuantificadores
        vars' = filter (\v -> v `notElem` fv t) vars