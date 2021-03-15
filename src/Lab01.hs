{-# LANGUAGE UnicodeSyntax, FlexibleInstances #-}

module Lab01(
  Formula (T, F, And, Or, Not, Iff, Implies, Prop),
  PropName,
  SATSolver,
  is_nnf,
  nnf,
  sat_dnf,
  satisfiable,
  dnf,
  tautology,
  update,
  eval,
  dnf2formula,
  prop_sat_dnf,
) where



import Control.Monad
import Data.List
import System.IO.Unsafe
import Test.QuickCheck

{-# ANN module "HLint: ignore Use camelCase" #-}

-- updating a function
update :: Eq a => (a -> b) -> a -> b -> a -> b
update ρ x v y = if x == y then v else ρ y

-- useful for debugging
debug :: Show a => String -> a -> a
debug str x =
  seq
    (unsafePerformIO $ do
       putStr "<"
       putStr str
       putStr ": "
       print x
       putStr ">")
    x

todo :: a
todo = todo

-- propositional variable names are just strings
type PropName = String

data Formula
  = T
  | F
  | Prop PropName -- atomic formulas
  | Not Formula
  | And Formula
        Formula
  | Or Formula
       Formula
  | Implies Formula
            Formula
  | Iff Formula
        Formula
  deriving (Eq, Show)

-- EXERCISE 1
-- truth valuations
type Valuation = PropName -> Bool


-- the evaluation function
eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Prop p) ρ = ρ p
eval (Not φ) ρ = not (eval φ ρ)
eval (And φ ψ) ρ = eval φ ρ && eval ψ ρ
eval (Or φ ψ) ρ = eval φ ρ || eval ψ ρ
eval (Implies φ ψ) ρ = eval (Or (Not φ) ψ) ρ
eval (Iff φ ψ) ρ = eval φ ρ == eval ψ ρ
eval _ _ = error "not a propositional formula"
-- end of Exercise 1

variables :: Formula -> [PropName]
variables = nub . go
  where
    go T = []
    go F = []
    go (Prop p) = [p]
    go (Not φ) = go φ
    go (And φ ψ) = go φ ++ go ψ
    go (Or φ ψ) = go φ ++ go ψ
    go (Implies φ ψ) = go φ ++ go ψ
    go (Iff φ ψ) = go φ ++ go ψ
    go _ = error "not a propositional formula"

type SATSolver = Formula -> Bool

-- the list of all valuations on a given list of variables
valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x:xs) =
  concat [[update ρ x True, update ρ x False] | ρ <- valuations xs]

satisfiable :: SATSolver
satisfiable φ = or [eval φ ρ | ρ <- valuations (variables φ)]

-- EXERCISE 2
tautology :: Formula -> Bool
tautology φ = and [eval φ ρ | ρ <- valuations (variables φ)]
-- End of Exercise 2

is_nnf :: Formula -> Bool
is_nnf T = True
is_nnf F = True
is_nnf (Prop _) = True
is_nnf (Not (Prop _)) = True
is_nnf (And phi psi) = is_nnf phi && is_nnf psi
is_nnf (Or phi psi) = is_nnf phi && is_nnf psi
is_nnf (Implies phi psi) = False
is_nnf (Iff phi psi) = False
is_nnf (Not _) = False
is_nnf _ = error "not a propositional formula"

-- EXERCISE 3
nnf :: Formula -> Formula
nnf (Prop propName) = Prop propName
nnf (Not (Prop propName)) = Not $ Prop propName
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = Or (nnf (Not phi)) (nnf psi)
nnf (Iff phi psi) =
  Or (And (nnf phi) (nnf psi)) (And (nnf (Not phi)) (nnf (Not psi)))
nnf (Not (And phi psi)) = Or (nnf (Not phi)) (nnf (Not psi))
nnf (Not (Or phi psi)) = And (nnf (Not phi)) (nnf (Not psi))
nnf (Not (Implies phi psi)) = let simp = nnf (Implies phi psi) in nnf (Not simp)
nnf (Not (Iff phi psi)) = let simp = nnf (Iff phi psi) in nnf (Not simp)
nnf (Not (Not phi)) = nnf phi
nnf (Not T) = F
nnf (Not F) = T
nnf T = T
nnf F = F
nnf _ = error "not a propositional formula"
-- End of Exercise 3


data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

type DNFClause = [Literal]
type DNF = [DNFClause]

dnf2formula :: [[Literal]] -> Formula
dnf2formula [] = F
dnf2formula lss = foldr1 Or (map go lss) where
  go [] = T
  go ls = foldr1 And (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)



-- EXERCISE 4
dnfHelper :: Formula -> DNF
dnfHelper T = [[]]
dnfHelper F = []
dnfHelper (Prop propName) = [ [Pos propName] ]
dnfHelper (Not (Prop propName)) = [ [Neg propName] ]
dnfHelper (And phi psi) =
  let a = dnfHelper phi
      b = dnfHelper psi
  in map (\[x,y] -> x ++ y) (sequence [a, b])
dnfHelper (Or phi psi) = dnfHelper phi ++ dnfHelper psi
dnfHelper _ = error "not a valid nnf formula"

dnf :: Formula -> DNF
dnf phi = let n = nnf phi in
  dnfHelper n
-- End of Exercise 4

sat_dnf :: SATSolver
sat_dnf input_formula =
  let dnf_instance = dnf input_formula
      formula_from_dnf = dnf2formula dnf_instance
  in satisfiable formula_from_dnf

prop_sat_dnf :: Formula -> Bool
prop_sat_dnf phi = sat_dnf phi == satisfiable phi
