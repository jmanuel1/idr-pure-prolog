{-
  An embeded DSL for prolog-style logic programming, based on the
  pure-prolog parser and interpreter originally written in Haskell

  Original author: Ken Friis Larsen      <kflarsen@diku.dk>
  Translated into Idris by Nathan Bedell <nbedell@tulane.edu>
-}

module Interp

import Ast
import Data.List

%default partial

----------------------------------------------------------------------
-- Interpreter
----------------------------------------------------------------------

public export
Unifier : Type
Unifier = List (Variable, Term)

-- A non-lazy version of maybe
public export
maybe' : b -> (a -> b) -> Maybe a -> b
maybe' n j Nothing  = n
maybe' n j (Just x) = j x

public export
subs : Unifier -> Term -> Term
subs u (Var x)   = maybe' (Var x) id (lookup x u)
subs u (Comp n ts) = Comp n $ map (subs u) ts

public export
compose : Unifier -> Unifier -> Unifier
compose u1 u2 = (map (\(v, t) => (v, subs u2 t)) u1) ++ u2

public export
occursIn : Variable -> Term -> Bool
occursIn v (Var x)     = v == x
occursIn v (Comp _ ms) = any (occursIn v) ms

mutual
  public export
  covering
  unify : Term -> Term -> Maybe Unifier
  unify (Var "_") t                         = pure []
  unify t (Var "_")                         = pure []
  unify (Var x) (Var y) with (x == y)
     unify (Var x) (Var y) | True           = pure []
     _ | False = pure [(x, Var y)]
  unify (Var x) t with (not (x `occursIn` t))
      unify (Var x) t   | True              = pure [(x, t)]
      _ | False = Nothing
  unify t v@(Var _)                         = unify v t
  unify (Comp m ms) (Comp n ns) with (m == n)
     unify (Comp m ms) (Comp n ns) | True   = unifyList ms ns
     _ | False = Nothing
  unify _ _ = Nothing

  public export
  unifyList : Terms -> Terms -> Maybe Unifier
  unifyList (t :: ts) (r :: rs) =
      do u1 <- unify t r
         u2 <- unifyList (map (subs u1) ts) (map (subs u1) rs)
  -- Note: I'm not sure if Idris supports backtick notation for operators
         pure $ u1 `compose` u2
  unifyList [] [] = Just []
  unifyList _ _   = Nothing

mutual
  public export
  vars : Term -> List Variable
  vars (Var "_") = []
  vars (Var x) = [x]
  vars (Comp _ ts) = varsList ts

  public export
  varsList : Terms -> List Variable
  varsList ts = [ v | t <- ts, v <- vars t]

public export
variables : Terms -> List Variable
variables ts = nub $ varsList ts

public export
freshen : List Variable -> (Term, Terms) -> (Term, Terms)
freshen bound (tc, tb) = (subs sub tc, map (subs sub) tb)
  where
    vars : List Variable
    vars = variables (tc :: tb)
    nextVar : Int -> Variable -> Variable
    nextVar i v =
      let v' = "_" ++ show i ++ "_" ++ v in
        if v' `elem` bound
          then nextVar (i+1) v
          else v'
    sub : Unifier
    sub = [ (v, Var (nextVar 0 v)) | v <- vars, v `elem` bound]

public export
data Solution : Type where
    MkSolution : List (Variable, Term) -> Solution

public export
implementation Eq Solution where
    (MkSolution x) == (MkSolution y) = assert_total $ x == y


public export
Show Solution where
  show (MkSolution [])            = "True"
  show (MkSolution xs ) = (concat $ intersperse "\n" $ map renderBindings xs)
    where renderBindings : (Variable, Term) -> String
          renderBindings (v, t) = v ++ " = " ++ show t


public export
isPlain : List Char -> Bool
isPlain (c :: cs) = isLower c && all (\c => c == '_' || isAlphaNum c) cs
isPlain [] = False

public export
data SearchTree : Type where
  Sol : Solution -> SearchTree
  Node : Goal -> List SearchTree -> SearchTree

public export
Eq SearchTree where
  (Sol x) == (Sol y) = assert_total $ x == y
  (Node x y) == (Node x' y') = assert_total $ (x == x') && (y == y')
  x == y = False

public export
isReportGoal : Term -> Bool
isReportGoal (Comp "_report" _) = True
isReportGoal _                  = False

public export
getSolution : Term -> Solution
getSolution (Comp "_report" args) = MkSolution sol
    where nontriv : (String, Term) -> Bool
          nontriv (x, (Var y)) with (x == y)
            nontriv (x, (Var y)) | True = False
            nontriv (x, (Var y)) | _ = True
          nontriv _ = True
          sol : ?
          sol = filter nontriv $ map (\ (Comp "=" [Comp v [], t]) => (v, t)) args
getSolution _ = MkSolution [("ERROR", Var "_Error")]

-- Uses the List monad for backtracking
public export
solve : Program -> Goal -> List SearchTree
solve prog [r] with (isReportGoal r)
    solve prog [r] | True  =  pure $ Sol $ getSolution r
    solve prog [r] | False = []
solve prog g@(t1 :: ts) = pure $ Node g trees
    where
      trees : List SearchTree
      trees = do
        c <- prog
        let (tc, tsc) = freshen (variables g) c
        case unify tc t1 of
         Just u => do
           let g' = map (subs u) $ tsc ++ ts
           solve prog g'
         Nothing => []

public export
makeReportGoal : Terms -> List Term
makeReportGoal goal = [Comp "_report" reportVars]
    where vars : List Variable
          vars = variables goal
          reportVars : Terms
          reportVars = map (\ v => Comp "=" [Comp v [], Var v]) vars

-- Use the trick of inserting an extra reporting goal
public export
makeReportTree : Program -> Goal -> SearchTree
makeReportTree prog goal = Node goal $ solve prog (goal ++ makeReportGoal goal)


----------------------------------------------------------------------
-- Traveral of Search Trees
----------------------------------------------------------------------

-- Depth first
public export
dfs : SearchTree -> List Solution
dfs (Sol sols) = [sols]
dfs (Node _ st) = [ s | t <- st, s <- dfs t]

-- Breath first
public export
bfs : SearchTree -> List Solution
bfs t = trav [t]
    where trav : List SearchTree -> List Solution
          trav [] = []
          trav ((Sol x) :: q) = x :: trav q
          trav ((Node _ st)  :: q) = trav (q ++ st)

-- Limited depth first
public export
limitedDfs : Int -> SearchTree -> List Solution
limitedDfs _ (Sol sols)  = [sols]
limitedDfs 0 _           = []
limitedDfs n (Node _ st) = [ s | t <- st, s <- limitedDfs (n-1) t]

-----------------------------------------------------------------------
--- Syntax for the DSL ---
-----------------------------------------------------------------------

-- Note: I might actually want to do something here like apply some
-- function to "h" and "b" here in order to supply some more syntatic
-- sugar.



-- syntax [h] ":-" [b] = (h, b)
infix 10 :-
export
(:-) : Term -> Terms -> Clause
head :- body = (head, body)


public export
empty : List Term
empty = []

-- syntax [p] "." = (p, empty)
-- suffix 10 .

export
data ProgramElement = Term | Clause

export
interface InterpProgramElement type (0 p : ProgramElement) | type where
  toClause : type -> Clause

export
InterpProgramElement Term Term where
  toClause p = (p, empty)

export
InterpProgramElement Clause Clause where
  toClause = id

public export
data DSLProgram : Type where
  Nil : DSLProgram
  (::) : InterpProgramElement type p => type -> DSLProgram -> DSLProgram

export
unDSL : DSLProgram -> Program
unDSL [] = []
unDSL (element :: elements) = toClause element :: unDSL elements

-- syntax "?-" [q] = nub $ bfs $ makeReportTree program [q]

prefix 10 ?-
export
(?-) : {auto program : Program} -> Term -> List Solution
(?-) {program} q = nub $ bfs $ makeReportTree program [q]
