module Common where

-- Comandos. Para evaluar evaluar o inicializar un expresión
data Stmt i = Def String i | Eval i deriving (Show)
  
instance Functor Stmt where
  fmap f (Def s i) = Def s (f i)
  fmap f (Eval i)  = Eval (f i)

-- Nombres
newtype Name =  Global String deriving (Show, Eq)

-- Entornos
type NameEnv v t = [(Name, (v, t))]

-- Tipos
{-
Cuando se estaba haciendo el printType surgió un problema, y fue necesario dividir el ForAllT en dos posibles casos 
debido a que es necesario distinguir entre '/\' y '\/', pero se debe mantener la 'igualdad' entre ambos.

En un inicia se usaba un mismo tipo para ambos, pero al querer imprimir había inconsistencia, por eso se unificaron en un nuevo 
constructor llamador Fat (el nombre viene de ForAllT). De esta forma los '/\' se representan con Lambd y los '\/' con Ty. 
-}
data Type = EmptyT 
          | FunT Type Type
          | BoundForAll Int
          | VarT String
          | ForAllT Fat
          | BoolT
          | NatT
          | ListTEmpty
          | ListT Type
          deriving (Show, Eq)

data Fat = Lambd Type | Ty Type deriving (Show)

instance Eq Fat where
    Ty t1 == Lambd t2 = t1 == t2
    Lambd t1 == Ty t2 = t1 == t2
    Ty t1 == Ty t2 = t1 == t2
    Lambd t1 == Lambd t2 = t1 == t2

-- Términos con nombres
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

-- Términos localmente sin nombres
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

-- Valores
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

-- Valores Numéricos
data NumVal = NZero | NSuc NumVal deriving (Show, Eq)

-- Valores Booleanos
data BoolVal = NTrue | NFalse deriving (Show, Eq)

-- Listas 
data ListVal val = VNil | VCons val (ListVal val) deriving (Show, Eq)

-- Contextos del tipado
type Context = [Type]
