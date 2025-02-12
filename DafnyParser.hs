{- | A Parser for MiniDafny
     ======================
-} 

module DafnyParser where

import Control.Applicative
import qualified Data.Char as Char
import Syntax
import Printer
import Parser (Parser)
import qualified Parser as P
import Test.HUnit  (runTestTT,Test(..),Assertion, (~?=), (~:), assert, Counts)



prop_roundtrip_val :: Value -> Bool
prop_roundtrip_val v = P.parse valueP (pretty v) == Right v

prop_roundtrip_exp :: Expression -> Bool
prop_roundtrip_exp e = P.parse expP (pretty e) == Right e

prop_roundtrip_stat :: Statement -> Bool
prop_roundtrip_stat s = P.parse statementP (pretty s) == Right s


wsP :: Parser a -> Parser a
wsP p= p <* many P.space

test_wsP :: Test
test_wsP = TestList [
  P.parse (wsP P.alpha) "a" ~?= Right 'a',
  P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc"
  ]


stringP :: String -> Parser ()
stringP s = P.string s *> many P.space *> pure ()

test_stringP :: Test
test_stringP = TestList [
  P.parse (stringP "a") "a" ~?= Right (),
  P.parse (stringP "a") "b" ~?= Left "No parses",
  P.parse (many (stringP "a")) "a  a" ~?= Right [(),()]
  ]

constP :: String -> a -> Parser a
constP s x = P.string s *> many P.space *> pure x

test_constP :: Test
test_constP = TestList [
  P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
  P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa"
  ]

parens :: Parser a -> Parser a
parens x = P.between (stringP "(") x (stringP ")")

braces :: Parser a -> Parser a
braces x = P.between (stringP "{") x (stringP "}")

brackets :: Parser a -> Parser a
brackets x = P.between (stringP "[") x (stringP "]")


valueP :: Parser Value
valueP = intValP <|> boolValP


intValP :: Parser Value
intValP = IntVal <$> P.int <* many P.space


boolValP :: Parser Value
boolValP = constP "true" (BoolVal True) <|> constP "false" (BoolVal False)


typeP :: Parser Type
typeP = constP "int" TInt <|> constP "bool" TBool <|> constP "array<int>" TArrayInt


expP :: Parser Expression
expP    = conjP where
  conjP   = compP `P.chainl1` opAtLevel (level Conj)  
  compP   = catP `P.chainl1` opAtLevel (level Gt)
  catP    = sumP `P.chainl1` opAtLevel (level Eq)
  sumP    = prodP `P.chainl1` opAtLevel (level Plus)
  prodP   = uopexpP `P.chainl1` opAtLevel (level Times)
  uopexpP = baseP
      <|> Op1 <$> uopP <*> uopexpP 
  baseP = lenP
       <|> Var <$> varP
       <|> parens expP
       <|> Val <$> valueP

opAtLevel :: Int -> Parser (Expression -> Expression -> Expression)
opAtLevel l = flip Op2 <$> P.filter (\x -> level x == l) bopP

varP :: Parser Var
varP = (Proj <$> nameP <*> brackets expP) <|> (Name <$> nameP)

lenP :: Parser Expression
lenP = (Op1 Len . Var . Name) <$> (nameP <* stringP ".Length")

reserved :: [String]
reserved = [ "assert", "break","else","Length"
 ,"false","for","function","invariant","if","in"
 ,"return","true","method","int", "bool"
 ,"while", "requires","ensures"]

nameP :: Parser Name
nameP = P.filter aux (wsP (some (P.alpha <|> P.digit <|> P.char '_')))

aux :: String -> Bool
aux s = s `notElem` reserved && not (Char.isDigit (head s))

uopP :: Parser Uop
uopP = constP "-" Neg <|>
       constP "!" Not <|>
       constP ".Length" Len


bopP :: Parser Bop
bopP = constP "==>" Implies <|>
       constP "<==>" Iff <|>
       constP "+" Plus <|>
       constP "-" Minus <|>
       constP "*" Times <|>
       constP "/" Divide <|>
       constP "%" Modulo <|>
       constP "==" Eq <|>
       constP "!=" Neq <|>
       constP ">=" Ge <|>
       constP ">" Gt <|>
       constP "<=" Le <|>
       constP "<" Lt <|>
       constP "&&" Conj <|>
       constP "||" Disj


bindingP :: Parser Binding
bindingP = toBind <$> nm <*> tp where 
     nm = (stringP "var" *> nameP) <|> nameP
     tp = stringP ":" *> typeP
     toBind x y = (x,y)

predicateP :: Parser Predicate
predicateP = Predicate <$> ex where ex = expP <|> lenP

statementP :: Parser Statement
statementP = emptyP <|> declP <|> assertP <|> assignP <|> ifP <|> whileP where 
     emptyP = constP ";" Empty
     declP = Decl <$> bindingP <* stringP ":=" <*> (expP <|> lenP)
     assertP = Assert <$> (stringP "assert" *> predicateP )
     assignP = Assign <$> varP <* stringP ":=" <*> (expP <|> lenP)
     ifP = If <$> (stringP "if" *> ((expP <|> lenP) <|> parens (expP <|> lenP))) 
          <*> blockP
          <*> ((stringP "else" *> blockP) <|> pure (Block []))
     whileP = doWhile <$> ex <*> inv <*> bl where
          ex = (stringP "while" *> ((expP <|> lenP) <|> parens (expP <|> lenP)))
          inv = invariantP
          bl = blockP
          doWhile e i b = While i e b 


invariantP :: Parser Predicate
invariantP = (stringP "invariant" *> predicateP) <|> pure (Predicate (Val (BoolVal True)))


blockP :: Parser Block
blockP = Block <$> braces (many statementP)

specificationP :: Parser Specification
specificationP = ens <|> req <|> modi where
     req = Requires <$> (stringP "requires" *> predicateP)
     ens = Ensures <$> (stringP "ensures" *> predicateP)
     modi = Modifies <$> (stringP "modifies" *> nameP)


methodP :: Parser Method
methodP = Method <$> nm <*> bi <*> br <*> bs <*> bl where
     nm = (stringP "method" *> nameP)
     bi = parens (P.sepBy bindingP (stringP ","))
     br = (stringP "returns" *> parens (P.sepBy bindingP (stringP ","))) <|> pure []
     bs = many specificationP
     bl = blockP

 

parseDafnyExp :: String -> Either P.ParseError Expression
parseDafnyExp = P.parse expP 

parseDafnyStat :: String -> Either P.ParseError Statement
parseDafnyStat = P.parse statementP

parseDafnyFile :: String -> IO (Either P.ParseError Method)
parseDafnyFile = P.parseFromFile (const <$> methodP <*> P.eof) 


test_comb = "parsing combinators" ~: TestList [
 P.parse (wsP P.alpha) "a" ~?= Right 'a',
 P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc",
 P.parse (stringP "a") "a" ~?= Right (),
 P.parse (stringP "a") "b" ~?= Left "No parses",
 P.parse (many (stringP "a")) "a  a" ~?= Right [(),()],
 P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
 P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa",
 P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]" ~?= Right [1,1,1]
 ]

test_value = "parsing values" ~: TestList [
 P.parse (many intValP) "1 2\n 3" ~?= Right [IntVal 1,IntVal 2,IntVal 3],
 P.parse (many boolValP) "true false\n true" ~?= Right [BoolVal True,BoolVal False,BoolVal True]
 ]

test_exp = "parsing expressions" ~: TestList [
 P.parse (many varP) "x y z" ~?= Right [Name "x", Name "y", Name "z"],
 P.parse (many nameP) "x sfds _" ~?= Right ["x","sfds", "_"],
 P.parse (many uopP) "- -" ~?=  Right [Neg,Neg],
 P.parse (many bopP) "+ >= .." ~?= Right [Plus,Ge]
 ]

test_stat = "parsing statements" ~: TestList [
 P.parse statementP ";" ~?= Right Empty,
 P.parse statementP "x := 3" ~?= Right (Assign (Name "x") (Val (IntVal 3))),
 P.parse statementP "if x { y := true; }" ~?=
    Right (If (Var (Name "x")) (Block [Assign (Name "y") (Val $ BoolVal True), Empty]) (Block [])),
 P.parse statementP "while 0 { }" ~?=
    Right (While (Predicate (Val (BoolVal True))) (Val (IntVal 0)) (Block []))
   ]


test_all :: IO Counts
test_all = runTestTT $ TestList [ test_comb, test_value, test_exp, test_stat]

