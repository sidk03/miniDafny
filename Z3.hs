{- | Z3 integration |
   ==================
-}
module Z3 where

import Syntax
import Data.List(intersperse)
import Text.PrettyPrint ( (<+>), Doc )
import qualified Text.PrettyPrint as PP

import System.Process(readProcessWithExitCode)
import Data.Set(Set)
import qualified Data.Set as Set

class PP a where
  pp :: a -> Doc

pretty :: PP a => a -> String
pretty = PP.render . pp




varExp :: Expression -> Set String
varExp (Var (Name nm)) = Set.singleton nm
varExp (Op1 _ exp) = varExp exp
varExp (Op2 exp1 _ exp2) = Set.union (varExp exp1) (varExp exp2)
varExp _ = Set.empty


level :: Bop -> Int
level Times  = 7
level Divide = 7
level Plus   = 5
level Minus  = 5
level Conj   = 1
level Disj   = 1
level Implies = 1
level Iff     = 1
level _      = 2

instance PP String where
  pp :: String -> Doc
  pp = PP.text

instance PP Int where
  pp :: Int -> Doc
  pp = PP.int

instance PP Bool where
  pp :: Bool -> Doc
  pp True = PP.text "true"
  pp False = PP.text "false"

instance PP Var where
  pp :: Var -> Doc
  pp (Name nm) = pp nm
  pp _ = PP.text "error"

instance PP Uop where
  pp :: Uop -> Doc
  pp Neg = PP.char '-'
  pp Not = PP.text "not"
  pp Len = PP.text ".Length"

instance PP Bop where
  pp :: Bop -> Doc
  pp Plus   = PP.char '+'
  pp Minus = PP.char '-'
  pp Times = PP.char '*'
  pp Divide = PP.text "div"
  pp Modulo = PP.text "mod"
  pp Eq = PP.char '='
  pp Neq = PP.text "disinct"
  pp Gt = PP.char '>'
  pp Ge = PP.text ">="
  pp Lt = PP.char '<'
  pp Le = PP.text "<="
  pp Conj = PP.text "and"
  pp Disj = PP.text "or"
  pp Implies = PP.text "=>"
  pp Iff = PP.char '='

instance PP Value where 
  pp (IntVal i) = pp i
  pp (BoolVal b) = pp b
  pp _ = PP.text "error"


isBase :: Expression -> Bool
isBase Val{} = True
isBase Var{} = True
isBase Op1{} = True
isBase _ = False

instance PP Expression where 
  pp :: Expression -> Doc
  pp (Var v) = pp v
  pp (Val v) = pp v
  pp (Op1 Len v) = PP.text "error"
  pp (Op1 o v) = PP.parens (pp o <+>  pp v)
  pp e@Op2{} = ppPrec 0 e  where
     ppPrec n (Op2 e1 bop e2) =
        PP.parens $
           pp bop <+> ppPrec (level bop) e1 <+>  ppPrec (level bop + 1) e2
     ppPrec _ e' = pp e'


toSMT :: Predicate -> String
toSMT (Predicate exp) = 
  let vars = Set.toList $ varExp exp in
  let doc1 = PP.vcat $ map(\x -> PP.parens $ PP.text "declare-const" <+> PP.text x <+> PP.text "Int") vars in 
  let doc2 = PP.parens (PP.text "assert" <> PP.parens (PP.text "not" <> pp exp)) in
  let doc3 = PP.parens $ PP.text "check-sat" in 
     PP.render (PP.vcat [doc1, doc2, doc3])
  
z3 :: String
z3 = "z3"

convertAndCheck :: Predicate -> String -> IO Bool
convertAndCheck p fn = do
  writeFile fn (toSMT p)
  (_exitCode, stdout, _stderr) <- readProcessWithExitCode z3 [fn] ""
  case stdout of
    's':'a':'t':_ -> return False
    'u':'n':'s':'a':'t':_ -> return True
    _ -> error $ "Z3 output was neither sat or unsat: " ++ stdout
