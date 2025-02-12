This is a parser and verify for a version of the dafny programming langauge. 
There is also implementation for a pretty printer 

The syntax for mini dafny is defined in the Syntax.hs file along with a pretty printer
The WP.hs file uses preconditions, postconditions and loop invariants to generate the weakest precondition
Z3.hs verified if a program is satisfiable using the Z3 algorithm