module PrettyPrinter ( printTerm, printType )
where

import  Common
import  Text.PrettyPrint.HughesPJ
import  Prelude hiding ((<>))


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
pp ii vs _ _ (Bound k)             = text (vs !! (ii - k - 1))
pp _  _  ii' vs' (Free (Global s)) = text s
pp ii vs ii' vs' (i :@: c) = 
  sep [parensIf (isLam i) (pp ii vs ii' vs' i), nest 1 (parensIf (isLam c || isApp c) (pp ii vs ii' vs' c))]

pp ii vs ii' vs' (Lam t c) =
  text "\\"
    <> text (vs !! ii)
    <> text ":"
    <> printType t
    <> text ". "
    <> pp (ii + 1) vs ii' vs' c

pp ii vs ii' vs' (ForAll term) = 
  text "/\\"
    <> text (vs' !! ii')
    <> text ". "
    <> pp ii vs (ii' + 1) vs' term

pp ii vs ii' vs' (TApp t typee) =
  parens (pp ii vs ii' vs' t)
    <> text " <"
    <> printType typee
    <> text ">"
  
pp ii vs ii' vs' t | isBool t  = printBool ii vs ii' vs' t
                   | isNat t   = printNat ii vs ii' vs' t
                   | otherwise = printList ii vs ii' vs' t


applyParen :: Int -> [String] -> Int -> [String] -> Term -> Doc
applyParen ii vs ii' vs' t = parensIf (not $ isAtom t) (pp ii vs ii' vs' t)

printBool :: Int -> [String] -> Int -> [String] -> Term -> Doc
printBool ii vs ii' vs' T = text "true" 
printBool ii vs ii' vs' F = text "false"
printBool ii vs ii' vs' (IfThenElse t1 t2 t3) =
  text "if "
    <> pp ii vs ii' vs' t1
    <> text " then "
    <> pp ii vs ii' vs' t2
    <> text " else "
    <> pp ii vs ii' vs' t3

printNat :: Int -> [String] -> Int -> [String] -> Term -> Doc
printNat ii vs ii' vs' Zero            = text "0"
printNat ii vs ii' vs' (Suc t@(Suc _)) = sep [text "suc", pp ii vs ii' vs' t]
printNat ii vs ii' vs' (Suc t)         = sep [text "suc", applyParen ii vs ii' vs' t]
printNat ii vs ii' vs' (Rec t u v)     = sep [text "R", applyParen ii vs ii' vs' t, applyParen ii vs ii' vs' u, applyParen ii vs ii' vs' v]
printNat ii vs ii' vs' t               = pp ii vs ii' vs' t

printList :: Int -> [String] -> Int -> [String] -> Term -> Doc
printList ii vs ii' vs' Nil          = text "nil"
printList ii vs ii' vs' (Cons t u)   = sep [text "cons", applyParen ii vs ii' vs' t, applyParen ii vs ii' vs' u]
printList ii vs ii' vs' (RecL t u v) = sep [text "RL", applyParen ii vs ii' vs' t, applyParen ii vs ii' vs' u, applyParen ii vs ii' vs' v]
printList ii vs ii' vs' t            = pp ii vs ii' vs' t

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
-- pretty-printer tipos

printForAllType :: Int -> Type -> Doc
printForAllType n (ForAllT typee) = parens $
  text "\\/ "
    <> text (cuantificadores !! n)
    <> text ". "
    <> printForAllType (n + 1) typee
printForAllType _ typee = printType typee

-- Empty
printType :: Type -> Doc
printType EmptyT = text "E"

-- Función
printType (FunT t1 t2) = sep [parensIf (isFun t1) (printType t1), text "->", printType t2]

-- Sistema F
printType (ForAllT typee) = printForAllType 0 (ForAllT typee)
printType (BoundForAll k) = text (cuantificadores !! k)

-- Bool
printType BoolT = text "Bool"

-- Nat
printType NatT = text "Nat"

-- List
printType (ListT t)    = text "List " <> parensIf (inList t) (printType t)
printType ListTEmpty = text "Lista Vacia"

isFun :: Type -> Bool
isFun (FunT _ _) = True
isFun _          = False

inList :: Type -> Bool
inList (ListT _)   = True
inList (FunT _ _)  = True
inList (ForAllT _) = True
inList _           = False

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
printTerm t = pp 0 (filter (\v -> v `notElem` fv t) vars) 0 cuantificadores t