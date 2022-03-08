module Main

import Interp
import Ast
import Examples
import Data.List

%default partial

nil : Term
nil = Comp "nil" []

cons : Term -> Term -> Term
cons head tail = Comp "cons" [head, tail]

append : Term -> Term -> Term -> Term
append xs ys res = Comp "append" [xs, ys, res]

Xs : Term
Xs = Var "Xs"

Y : Term
Y = Var "Y"

Ys : Term
Ys = Var "Ys"

Rec : Term
Rec = Var "Rec"

program2 : Program
program2 = unDSL
  [ append nil Ys Ys
  , append (cons X Xs) Ys (cons X Rec) :- [append Xs Ys Rec]
  ]

-- Some tests
main : IO ()
main = do
  putStrLn "\n--------------- append empty right"
  print $ (nub $ bfs $ makeReportTree program2 [append (cons X nil) nil Rec])
  putStrLn "\n--------------- append empty left"
  print $ (nub $ bfs $ makeReportTree program2 [append nil Xs Rec])
  putStrLn "\n--------------- append example"
  printLn $ (nub $ bfs $ makeReportTree program2 [append (cons X nil) (cons Y (cons p nil)) Rec])
