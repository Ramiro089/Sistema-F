module Common where

-- Comandos interactivos
data Stmt i = Def String i | Eval i deriving (Show)
  
instance Functor Stmt where
  fmap f (Def s i) = Def s (f i)
  fmap f (Eval i)  = Eval (f i)

-- Tipos de los nombres
data Name =  Global String deriving (Show, Eq)

-- Entornos
type NameEnv v t = [(Name, (v, t))]

-- Tipos (T)
data Type = EmptyT 
          | ListTEmpty
          | FunT Type Type
          -- Sistema F
          | BoundForAll Int
          | VarT String
          | ForAllT Type
          -- Tipos
          | BoolT
          | NatT
          | ListT Type
          deriving (Show, Eq)
  
-- Términos con nombres (t)
data LamTerm  =  LVar String
              |  LAbs String Type LamTerm
              |  LApp LamTerm LamTerm
              -- Sistema F
              |  LTAbs String LamTerm
              |  LTApp LamTerm Type
              -- Bool
              | LTrue 
              | LFalse
              | LIfThenElse LamTerm LamTerm LamTerm
              -- Nat 
              |  LZero
              |  LSuc LamTerm
              |  LRec LamTerm LamTerm LamTerm
              -- List
              |  LNil
              |  LCons LamTerm LamTerm
              |  LRecL LamTerm LamTerm LamTerm
              deriving (Show, Eq)

-- Términos localmente sin nombres (t)
data Term  = Bound Int
           | Free Name 
           | Term :@: Term
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

-- Valores (v)
data Value = VLam Type Term
           --Sistema F
           | VForAll Term
           -- Bool
           | VBool BoolVal
           -- Nat
           | VNum NumVal
           -- List
           | VList (ListVal Value)
         deriving (Show, Eq)

-- Valores Numericos
data NumVal = NZero | NSuc NumVal deriving (Show, Eq)

-- Valores Booleanos
data BoolVal = NTrue | NFalse deriving (Show, Eq)

-- Listas 
data ListVal val = VNil | VCons val (ListVal val) deriving (Show, Eq)

-- Contextos del tipado
type Context = [Type]
