{-
  An embeded DSL for prolog-style logic programming, based on the
  pure-prolog parser and interpreter originally written in Haskell

  Original author: Ken Friis Larsen      <kflarsen@diku.dk>
  Translated into Idris by Nathan Bedell <nbedell@tulane.edu>
-}

module Ast

import Data.List

----------------------------------------------------------------------
-- Abstract Syntax Tree
----------------------------------------------------------------------

public export
Atom : Type
Atom = String

public export
Variable : Type
Variable = String

public export
data Term : Type where
 Var : Variable -> Term
 Comp : Atom -> (args: List Term) -> Term

public export
and' : (l : List Bool) -> Bool
and' xs = foldr p True xs
  where
    p : Bool -> Bool -> Bool
    p True True = True
    p x y = False

public export
implementation Eq Term where
  (Var x) == (Var y) = assert_total $ x == y
  (Comp x y) == (Comp x' y') = assert_total $ (x == x') && (and' $ zipWith (==) y y')
  x == y = assert_total $ False

public export
implementation Show Term where
  show (Var s) = s
  show (Comp s []) = s
  show (Comp s xs) = s ++ "(" ++ (concat $ intersperse "," (map (\x => show (assert_smaller xs x)) xs)) ++ ")"

public export
Terms : Type
Terms = List Term

public export
Clause : Type
Clause = (Term, Terms) -- head and body

public export
Clauses : Type
Clauses = List Clause

public export
Goal : Type
Goal = List Term

public export
Program : Type
Program = Clauses
