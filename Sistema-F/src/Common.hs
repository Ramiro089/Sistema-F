{-# OPTIONS_GHC -Wno-missing-export-lists #-}   -- De este modulo importo todo
-- | Define la forma que tendrán los valores, términos y tipos del Sistema F
module Common
where

-- | Comandos, usados para evaluar o definir un expresión
data Stmt i = Def String i | Eval i deriving (Show)
  
instance Functor Stmt where
  fmap f (Def s i) = Def s (f i)
  fmap f (Eval i)  = Eval (f i)

-- | Entornos usado durante la evaluación
type NameEnv v t = [(String, (v, t))]

-- | Tipos que poseen las expresiones
data Type = EmptyT 
          | FunT Type Type        
          | BoundForAll Pos
          | VarT String
          | ForAllT Fat
          | BoolT
          | NatT
          | ListTEmpty
          | ListT Type
          deriving (Show, Eq)

{- | Formas de estar ligado a un para todos

External e Inner son iguales entre si
-}
data Pos = External Int | Inner Int deriving (Show)   
instance Eq Pos where
    External t1 == Inner t2    = t1 == t2
    Inner t1    == External t2 = t1 == t2
    External t1 == External t2 = t1 == t2
    Inner t1    == Inner t2    = t1 == t2

{- | Forma de distinguir los distintos para todos

Fat viene de ForAllT, Lambd viene de Lambda, Lt viene de LamTerm, Ty viene de Type

Lambd, Lt y Ty son iguales entre si

-}
data Fat = Lambd Type | Lt String Type | Ty Type deriving (Show)    
instance Eq Fat where
    Ty  t1   == Lambd t2 = t1 == t2
    Lambd t1 == Ty  t2   = t1 == t2
    Lt _ t1  == Lambd t2 = t1 == t2
    Lambd t1 == Lt _ t2  = t1 == t2
    Ty t1    == Lt _ t2  = t1 == t2
    Lt _ t1  == Ty t2    = t1 == t2

    Lt s t1  == Lt s' t2 = t1 == t2 && s == s'
    Ty t1    == Ty t2    = t1 == t2
    Lambd t1 == Lambd t2 = t1 == t2

-- | Lambda términos con nombres
data LamTerm = LVar String
             | LAbs String Type LamTerm
             | LApp LamTerm LamTerm
             -- Sistema F
             | LTAbs String LamTerm
             | LTApp LamTerm Type
             -- Bool
             | LTrue 
             | LFalse
             | LIfThenElse LamTerm LamTerm LamTerm
             -- Nat
             | LZero
             | LSuc LamTerm
             | LRec LamTerm LamTerm LamTerm
             -- List
             | LNil
             | LCons LamTerm LamTerm
             | LRecL LamTerm LamTerm LamTerm
             deriving (Show, Eq)

-- | Lambda términos localmente sin nombres
data Term = Bound Int
          | FreeGlobal String
          | App Term Term
          | Lam Type Term
          -- Sistema F
          | ForAll Term
          | TApp Term Type
          -- Bool
          | T
          | F
          | IfThenElse Term Term Term
          -- Nat
          | Zero
          | Suc Term
          | Rec Term Term Term
          -- List
          | Nil
          | Cons Term Term
          | RecL Term Term Term
          deriving (Show, Eq)

-- | Valores que puede asumir una expresión
data Value = VLam Type Term
           -- Sistema F
           | VForAll Term
           -- Bool
           | VBool BoolVal
           -- Nat
           | VNum NumVal
           -- List
           | VList (ListVal Value)
           deriving (Show, Eq)

-- | Valores Numéricos
data NumVal = NZero | NSuc NumVal deriving (Show, Eq)

-- | Valores Booleanos
data BoolVal = NTrue | NFalse deriving (Show, Eq)

-- | Valores Listas 
data ListVal val = VNil | VCons val (ListVal val) deriving (Show, Eq)