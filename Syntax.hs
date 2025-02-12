{- | Mini Dafny - Syntax |
   -----------------------
-}

module Syntax where

import Data.List(intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad(mapM_)
import qualified Data.Char as Char

import Test.HUnit



data Method = Method Name [Binding] [Binding] [Specification] Block
  deriving (Eq, Show)


type Name = String     

type Binding = (Name, Type)


data Type = TInt | TBool | TArrayInt
  deriving (Eq, Ord, Show)


data Specification =
    Requires Predicate
  | Ensures  Predicate
  | Modifies Name
  deriving (Eq, Show)


newtype Predicate = Predicate Expression
  deriving (Eq, Show)


newtype Block = Block [ Statement ]         
  deriving (Eq, Show)


instance Semigroup Block where
   (<>) :: Block -> Block -> Block
   Block s1 <> Block s2 = Block (s1 <> s2)
instance Monoid Block where
   mempty :: Block
   mempty = Block []


data Statement =
    Decl Binding Expression         
  | Assert Predicate                 
  | Assign Var Expression              
  | If Expression Block Block         
  | While Predicate Expression Block  
  | Empty                             
  deriving (Eq, Show)


data Expression =
    Var Var                            -- global variables x and array indexing
  | Val Value                          -- literal values
  | Op1 Uop Expression                 -- unary operators
  | Op2 Expression Bop Expression      -- binary operators
  deriving (Eq, Ord, Show)



data Value =
    IntVal Int         -- 1
  | BoolVal Bool       -- false, true
  | ArrayVal [Int]
  deriving (Eq, Show, Ord)



data Uop =
    Neg   -- `-` :: Int -> Int
  | Not   -- `!` :: a -> Bool
  | Len   -- `.Length` :: Table -> Int
  deriving (Eq, Ord, Show, Enum, Bounded)


data Bop =
    Plus     -- `+`  :: Int -> Int -> Int
  | Minus    -- `-`  :: Int -> Int -> Int
  | Times    -- `*`  :: Int -> Int -> Int
  | Divide   -- `/`  :: Int -> Int -> Int   -- floor division
  | Modulo   -- `%`  :: Int -> Int -> Int   -- modulo
  | Eq       -- `==` :: Int -> Int -> Bool
  | Neq      -- `!=` :: Int -> Int -> Bool> 
  | Gt       -- `>`  :: Int -> Int -> Bool
  | Ge       -- `>=` :: Int -> Int -> Bool
  | Lt       -- `<`  :: Int -> Int -> Bool
  | Le       -- `<=` :: Int -> Int -> Bool
  | Conj     -- `&&` :: Bool -> Bool -> Bool
  | Disj     -- `||` :: Bool -> Bool -> Bool
  | Implies  -- `==>` :: Bool -> Bool -> Bool
  | Iff      -- `<==>` :: Bool -> Bool -> Bool
  deriving (Eq, Ord, Show, Enum, Bounded)


data Var =
    Name Name            -- x, global variable
  | Proj Name Expression -- a[1], access array table using an integer
  deriving (Eq, Ord, Show)


wMinMax = Method "MinMax" [("x",TInt),("y",TInt)] [("min",TInt),("max",TInt)] [Ensures (Predicate (Op2 (Op2 (Op2 (Var (Name "min")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "min")) Le (Var (Name "y")))) Conj (Op2 (Op2 (Var (Name "min")) Eq (Var (Name "x"))) Disj (Op2 (Var (Name "min")) Eq (Var (Name "y")))))),Ensures (Predicate (Op2 (Op2 (Op2 (Var (Name "max")) Ge (Var (Name "x"))) Conj (Op2 (Var (Name "max")) Ge (Var (Name "y")))) Conj (Op2 (Op2 (Var (Name "max")) Eq (Var (Name "x"))) Disj (Op2 (Var (Name "max")) Eq (Var (Name "y"))))))] (Block [If (Op2 (Var (Name "x")) Lt (Var (Name "y"))) (Block [Assign (Name "min") (Var (Name "x")),Empty,Assign (Name "max") (Var (Name "y")),Empty]) (Block [Assign (Name "max") (Var (Name "x")),Empty,Assign (Name "min") (Var (Name "y")),Empty])])

wLoopToZero = Method "LoopToZero" [("m",TInt),("p",TInt)] [("x",TInt),("z",TInt)] [Requires (Predicate (Op2 (Var (Name "m")) Gt (Val (IntVal 0)))),Ensures (Predicate (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "p")) Minus (Var (Name "m")))))] (Block [Assign (Name "x") (Var (Name "m")),Empty,Assign (Name "z") (Var (Name "p")),Empty,While (Predicate (Op2 (Op2 (Var (Name "x")) Ge (Val (IntVal 0))) Conj (Op2 (Op2 (Var (Name "z")) Minus (Var (Name "x"))) Eq (Op2 (Var (Name "p")) Minus (Var (Name "m")))))) (Op2 (Var (Name "x")) Gt (Val (IntVal 0))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Minus (Val (IntVal 1))),Empty,Assign (Name "x") (Op2 (Var (Name "x")) Minus (Val (IntVal 1))),Empty])])

wTwoLoops = Method "TwoLoops" [("a",TInt),("b",TInt),("c",TInt)] [("x",TInt),("y",TInt),("z",TInt)] [Requires (Predicate (Op2 (Op2 (Op2 (Var (Name "a")) Gt (Val (IntVal 0))) Conj (Op2 (Var (Name "b")) Gt (Val (IntVal 0)))) Conj (Op2 (Var (Name "c")) Gt (Val (IntVal 0))))),Ensures (Predicate (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "b"))) Plus (Var (Name "c")))))] (Block [Assign (Name "x") (Val (IntVal 0)),Empty,Assign (Name "y") (Val (IntVal 0)),Empty,Assign (Name "z") (Var (Name "c")),Empty,While (Predicate (Op2 (Op2 (Op2 (Var (Name "x")) Le (Var (Name "a"))) Conj (Op2 (Var (Name "y")) Eq (Val (IntVal 0)))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "x")) Plus (Var (Name "y"))) Plus (Var (Name "c")))))) (Op2 (Var (Name "x")) Lt (Var (Name "a"))) (Block [Assign (Name "x") (Op2 (Var (Name "x")) Plus (Val (IntVal 1))),Empty,Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))),Empty]),While (Predicate (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "b"))) Conj (Op2 (Var (Name "x")) Eq (Var (Name "a")))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "a")) Plus (Var (Name "y"))) Plus (Var (Name "c")))))) (Op2 (Var (Name "y")) Lt (Var (Name "b"))) (Block [Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1))),Empty,Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))),Empty])])

wSquare = Method "Square" [("x",TInt)] [("z",TInt)] [Requires (Predicate (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))),Ensures (Predicate (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))))] (Block [Decl ("y",TInt) (Val (IntVal 0)),Empty,Assign (Name "z") (Val (IntVal 0)),Empty,While (Predicate (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) (Op2 (Var (Name "y")) Lt (Var (Name "x"))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Plus (Var (Name "x"))),Empty,Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1))),Empty])])

wSquareRoot = Method "SquareRoot" [("x",TInt)] [("z",TInt)] [Requires (Predicate (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))),Ensures (Predicate (Op2 (Op2 (Op2 (Var (Name "z")) Times (Var (Name "z"))) Le (Var (Name "x"))) Conj (Op2 (Var (Name "x")) Lt (Op2 (Op2 (Var (Name "z")) Plus (Val (IntVal 1))) Times (Op2 (Var (Name "z")) Plus (Val (IntVal 1)))))))] (Block [Assign (Name "z") (Val (IntVal 0)),Empty,While (Predicate (Op2 (Op2 (Var (Name "z")) Times (Var (Name "z"))) Le (Var (Name "x")))) (Op2 (Op2 (Op2 (Var (Name "z")) Plus (Val (IntVal 1))) Times (Op2 (Var (Name "z")) Plus (Val (IntVal 1)))) Le (Var (Name "x"))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Plus (Val (IntVal 1))),Empty])])

wIntDiv = Method "IntDiv" [("m",TInt),("n",TInt)] [("d",TInt),("r",TInt)] [Requires (Predicate (Op2 (Var (Name "n")) Gt (Val (IntVal 0)))),Ensures (Predicate (Op2 (Var (Name "m")) Eq (Op2 (Op2 (Var (Name "d")) Times (Var (Name "n"))) Plus (Var (Name "r"))))),Ensures (Predicate (Op2 (Op2 (Val (IntVal 0)) Le (Var (Name "r"))) Conj (Op2 (Var (Name "r")) Lt (Var (Name "n")))))] (Block [Assign (Name "d") (Op2 (Var (Name "m")) Divide (Var (Name "n"))),Empty,Assign (Name "r") (Op2 (Var (Name "m")) Modulo (Var (Name "n"))),Empty])
 

class PP a where
  pp :: a -> Doc


pretty :: PP a => a -> String
pretty = PP.render . pp

oneLine :: PP a => a -> String
oneLine = PP.renderStyle (PP.style {PP.mode=PP.OneLineMode}) . pp


instance PP Uop where
  pp Neg = PP.char '-'
  pp Not = PP.char '!'
  pp Len = PP.text ".Length"


{- | Pretty-Pretter implementation |
   ---------------------------------
-}

instance PP String where
  pp = PP.text

instance PP Int where
  pp = PP.int

instance PP Bool where
  pp True = PP.text "true"
  pp False = PP.text "false"


instance PP [Int] where
  pp xs = PP.brackets $ PP.hcat $ intersperse (PP.text ",") (map PP.int xs)

instance PP Value where
  pp (IntVal i)  = pp i
  pp (BoolVal b) = pp b
  pp (ArrayVal l)  = pp l

instance PP Bop where
  pp Plus   = PP.char '+'
  pp Minus = PP.char '-'
  pp Times = PP.char '*'
  pp Divide = PP.char '/'
  pp Modulo = PP.char '%'
  pp Eq = PP.text "=="
  pp Neq = PP.text "!="
  pp Gt = PP.char '>'
  pp Ge = PP.text ">="
  pp Lt = PP.char '<'
  pp Le = PP.text "<="
  pp Conj = PP.text "&&"
  pp Disj = PP.text "||"
  pp Implies = PP.text "==>"
  pp Iff = PP.text "<->"


instance PP Type where
  pp TInt  = PP.text "int"
  pp TBool = PP.text "bool"
  pp TArrayInt = PP.text "array<int>"

instance PP Binding where
  pp (x, t) = PP.text x <+> PP.text ":" <+> pp t


instance PP Expression where
  pp (Var v) = pp v
  pp (Val v) = pp v
  pp (Op1 Len v@(Var _)) = pp v <> pp Len
  pp (Op1 Len v) = PP.parens (pp v) <> pp Len  
  pp (Op1 o v) = pp o <+> if isBase v then pp v else PP.parens (pp v)
  pp e@Op2{} = ppPrec 0 e  where
     ppPrec n (Op2 e1 bop e2) =
        ppParens (level bop < n) $
           ppPrec (level bop) e1 <+> pp bop <+> ppPrec (level bop + 1) e2
     ppPrec _ e' = pp e'
     ppParens b = if b then PP.parens else id

isBase :: Expression -> Bool
isBase Val{} = True
isBase Var{} = True
isBase Op1{} = True
isBase _ = False

level :: Bop -> Int
level Times  = 7
level Divide = 7
level Plus   = 5
level Minus  = 5
level Conj   = 3
level _      = 2    


instance PP Var where
  pp (Name name) = PP.text name 
  pp (Proj expression idx) = pp expression <> PP.brackets (pp idx)


instance PP Block where
  pp (Block statements) = PP.vcat (map pp statements)


instance PP Statement where
  pp (Decl (name, ty) expr)  = PP.text "var" <+> PP.text name <+> PP.text ":" <+> pp ty <+> PP.text ":=" <+> (pp expr <> PP.char ';')
  pp (New (name, ty) size)   = PP.text "var" <+> PP.text name <+> PP.text ":" <+> pp ty <+> PP.text ":=" <+> PP.text "new" <+> (pp ty <> PP.brackets (pp size) <> PP.char ';')
  pp (Assert pred)           = PP.text "(assert" <+> (pp pred <> PP.char ')')
  pp (Assign var expr)       = pp var <+> PP.text ":=" <+> (pp expr <> PP.char ';')
  pp (If cond thenBlock elseBlock) 
    | elseBlock == Block [] = PP.text "if" <+> PP.parens (pp cond) <+> PP.lbrace PP.$+$ (pp thenBlock) PP.$+$ PP.rbrace
    | otherwise = PP.text "if" <+> PP.parens (pp cond) <+> PP.lbrace PP.$+$ (pp thenBlock) PP.$+$ PP.rbrace
    <+> PP.text "else" <+> PP.lbrace PP.$+$ (pp elseBlock) PP.$+$ PP.rbrace 
  pp (While invariants cond block) 
    | invariants == [] = PP.text "while" <+> PP.parens (pp cond) PP.$+$ PP.braces (pp block)
    | otherwise = PP.text "while" <+> PP.parens (pp cond) PP.$+$ (PP.vcat $ map (\ln -> PP.text "invariant" <+> pp ln) invariants) PP.$+$ PP.braces (pp block)
  pp Empty                   = PP.empty


instance PP Predicate where
  pp (Predicate [] expr) = pp expr
  pp (Predicate bindings expr) = PP.text "forall" <+> (PP.hcat $ intersperse (PP.text ", ") (map ppBinding bindings)) <+> PP.text "::" <+> PP.parens (pp expr)
    where
      ppBinding (name, ty) = PP.text name <+> PP.text ":" <+> pp ty

instance PP Method where
  pp (Method name inputs outputs specs block) =
    PP.text "method" <+> PP.text name
    <+> PP.parens (PP.hcat $ intersperse (PP.text ", ") (map ppBinding inputs))
    <+> PP.text "returns" <+> PP.parens (PP.hcat $ intersperse (PP.text ", ") (map ppBinding outputs))
    PP.$+$ (PP.vcat (map pp specs) ) PP.$+$ PP.lbrace PP.$+$ (pp block) PP.$+$ PP.rbrace 
    where
      ppBinding (name, ty) = PP.text name <+> PP.text ":" <+> pp ty


instance PP Specification where
  pp (Requires pred) = PP.text "requires" <+> (pp pred) 
  pp (Ensures pred)  = PP.text "ensures" <+> (pp pred) 
  pp (Modifies name) = PP.text "modifies" <+> (PP.text name) 


