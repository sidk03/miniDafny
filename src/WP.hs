{- | Weakest Preconditions |
   =========================
-}

module WP where

import Printer
import Syntax

import Test.HUnit
import Data.Type.Bool (Not)

class Subst a where
  subst :: a -> Name -> Expression -> a


instance Subst Expression where
  subst (Var (Proj _ _)) _ _ = error "Ignore arrays for this project"
  subst (Var (Name nm1) ) nm2 sub = if nm1 == nm2 then sub else Var(Name nm1)
  subst (Val x) _ _ = Val x
  subst (Op1 ux exp) nm sub= Op1 ux (subst exp nm sub)
  subst (Op2 exp1 bp exp2) nm sub = Op2 (subst exp1 nm sub) bp (subst exp2 nm sub)



wInv :: Expression
wInv =  Op2 (Op2 (Var (Name "y")) Le (Var (Name "x")))
            Conj
            (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))
            


wYPlus1 :: Expression
wYPlus1 = Op2 (Var (Name "y")) Plus (Val (IntVal 1))

wInvSubstYY1 :: Expression
wInvSubstYY1 = Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x")))
                   Conj
                   (Op2 (Var (Name "z")) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))

test_substExp :: Test
test_substExp = TestList [ "exp-subst" ~: subst wInv "y" wYPlus1 ~?= wInvSubstYY1 ]


instance Subst Predicate where
  subst (Predicate exp) nm sub = Predicate (subst exp nm sub)

test_substPred :: Test
test_substPred = TestList [ "pred-subst" ~: subst (Predicate wInv) "y" wYPlus1 ~?= Predicate wInvSubstYY1 ]



class WP a where
  wp :: a -> Predicate -> Predicate



instance WP Statement where
  wp (Assert _) p = error "Ignore assert for this project"
  wp (Assign (Proj _ _) _) p = error "Ignore arrays for this project"
  wp (Assign (Name nm) exp) p = subst p nm exp
  wp (Decl (nm, tp) exp) p = subst p nm exp
  wp Empty p = p 
  wp (If con b_if (Block[])) p = Predicate (Op2 con Implies bf) 
    where Predicate bf = wp b_if p
  wp (If con b_if b_el) p = 
    let Predicate b1 = wp b_if p 
        Predicate b2 = wp b_el p in 
      Predicate (Op2 (Op2 con Implies b1) Conj (Op2 (Op1 Not con) Implies b2))
  wp (While inv exp bl) _ = inv 
    

instance WP Block where
  wp :: Block -> Predicate -> Predicate
  wp (Block stb) p = foldr (\a b -> wp a b) p stb


wSquareWhile :: Statement 
wSquareWhile = While (Predicate (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x")))))) (Op2 (Var (Name "y")) Lt (Var (Name "x"))) (Block [Assign (Name "z") (Op2 (Var (Name "z")) Plus (Var (Name "x"))),Empty,Assign (Name "y") (Op2 (Var (Name "y")) Plus (Val (IntVal 1))),Empty])

wWhilePost :: Expression
wWhilePost = Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))


vcsWhile :: [Predicate]
vcsWhile =
  [ Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op2 (Var (Name "y")) Lt (Var (Name "x")))) Implies (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x"))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Var (Name "x"))) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))))
  ,Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op1 Not (Op2 (Var (Name "y")) Lt (Var (Name "x"))))) Implies (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))))]

test_vcStmt :: Test
test_vcStmt =
  TestList [ "vc - while" ~: vcStmt (Predicate wWhilePost) wSquareWhile ~?= vcsWhile ]

vcStmt :: Predicate -> Statement -> [Predicate]
vcStmt (Predicate p) (While (Predicate inv) e b) = 
  let (Predicate bl) = wp b (Predicate inv) 
      p1 = Predicate (Op2 (Op2 inv Conj e) Implies bl)
      p2 = Predicate (Op2 (Op2 inv Conj (Op1 Not e)) Implies p) in
        [p1,p2]

vcStmt _ _ = []

vcBlock :: Predicate -> Block -> [Predicate]
vcBlock p (Block x) = fst (foldr (\e (ls,pr) -> ((vcStmt pr e)++ls, wp e p)) ([],p) x)


requires :: [Specification] -> Expression
requires [] = Val (BoolVal True)
requires (Requires (Predicate e) : ps) = Op2 e Conj (requires ps)
requires (_ : ps) = requires ps

ensures :: [Specification] -> Expression
ensures [] = Val (BoolVal True)
ensures (Ensures (Predicate e) : ps) = Op2 e Conj (ensures ps)
ensures (_ : ps) = ensures ps


vc :: Method -> [Predicate] 
vc (Method _ _ _ specs (Block ss)) =
  let e = ensures specs
      r = requires specs
  in
    let Predicate pr  = wp (Block ss) (Predicate e) in 
      (Predicate (Op2 r Implies pr)) : vcBlock (Predicate e) (Block ss)


vcSquare :: [Predicate]
vcSquare = [ Predicate (Op2 (Op2 (Op2 (Var (Name "x")) Gt (Val (IntVal 0))) Conj (Val (BoolVal True))) Implies (Op2 (Op2 (Val (IntVal 0)) Le (Var (Name "x"))) Conj (Op2 (Val (IntVal 0)) Eq (Op2 (Val (IntVal 0)) Times (Var (Name "x"))))))
           , Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op2 (Var (Name "y")) Lt (Var (Name "x")))) Implies (Op2 (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Le (Var (Name "x"))) Conj (Op2 (Op2 (Var (Name "z")) Plus (Var (Name "x"))) Eq (Op2 (Op2 (Var (Name "y")) Plus (Val (IntVal 1))) Times (Var (Name "x"))))))
           , Predicate (Op2 (Op2 (Op2 (Op2 (Var (Name "y")) Le (Var (Name "x"))) Conj (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "y")) Times (Var (Name "x"))))) Conj (Op1 Not (Op2 (Var (Name "y")) Lt (Var (Name "x"))))) Implies (Op2 (Op2 (Var (Name "z")) Eq (Op2 (Var (Name "x")) Times (Var (Name "x")))) Conj (Val (BoolVal True))))]

test_vc_method :: Test
test_vc_method = TestList [ "vc square" ~: vc wSquare ~?= vcSquare ]

