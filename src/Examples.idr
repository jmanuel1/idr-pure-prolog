{-
  An embeded DSL for prolog-style logic programming, based on the
  pure-prolog parser and interpreter originally written in Haskell

  Original author: Ken Friis Larsen      <kflarsen@diku.dk>
  Translated into Idris by Nathan Bedell <nbedell@tulane.edu>
-}

import Interp
import Ast
import Data.List

%default partial

public export
p : Term
p = Comp "p" []

public export
q : Term
q = Comp "q" []

public export
x : Term
x = Comp "x" []

public export
z : Term
z = Comp "z" []

public export
r : Term -> Term
r x = Comp "r" [x]

public export
n : Term -> Term
n x = Comp "n" [x]

public export
X : Term
X = Var "X"

public export
s : Term -> Term
s x = Comp "s" [x]

public export
f : Term -> Term -> Term
f x y = Comp "f" [x, y]

public export
%hint
program : Program
program = unDSL
  [ p
    , q :- [p]
    , (n z)
    , (n (s X)) :- [n X]
    , (f z z)
    , (f z (s z))
    , (f X X)
  ]

public export
result : List Solution
result = nub $ bfs $ makeReportTree program [f z X]

-- Note: I should make this more type-safe.
public export
getSolutions : List Solution -> List Term
getSolutions xs = concat $ map getSolution xs
  where getSolution : Solution -> List Term
        getSolution (MkSolution x) = map snd x

public export
f_val : Term -> List Term
f_val x = getSolutions $ nub $ bfs $ makeReportTree program [f x X]

public export
nat : Term -> Bool
nat t = query /= []
  where query : List Solution
        query = ?- n t

-- This is a version of f_val that runs on our embedded prolog
-- system, but only allows values of type Nat.
public export
f_val' : (x : Term) -> {auto p : True = nat x} -> List Term
f_val' x = getSolutions $ ?- f x X

-- An example. The following (should) compile.
-- However, the compiler doesn't like when I try to assert this total. It does strange things.
-- val : List Term
-- val = f_val' z

-- The following does not compile.
-- val' : List Term
-- val' = f_val' (s z)
