# Lab01

Unicode input: type "\\varphi" to obtain φ, "\\rho" for ρ, and similarly for other mathematical characters.

# Imports and utility functions

```haskell id=64937988-5a01-4873-b337-1d6159c293b7
{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances #-}

import Data.List
import Control.Monad
import Test.QuickCheck
import System.IO.Unsafe

-- updating a function
update :: Eq a => (a -> b) -> a -> b -> a -> b
update ρ x v = \y -> if x == y then v else ρ y

-- useful for debugging
debug :: Show a => String -> a -> a
debug str x = seq (unsafePerformIO $ do putStr "<"; putStr str; putStr ": "; print x; putStr ">") x

todo :: a
todo = todo
```

**WARNING**: Do not run cells containing "todo", since it will run forever requiring to reset the virtual machine.

# Syntax

We define an inductive type for formulas of first-order logic.

For propositional logic we will only use atomic formulas of the form "Rel RelName \[\]", i.e., zero-ary relations, and no quantifiers. It's convenient to have here a more general definition since later we will use it for first-order logic.

```haskell id=573eb208-5c0a-4964-beed-5a54dbc80ee1
-- propositional variable names are just strings
type PropName = String

data Formula =
      T
    | F
    | Prop PropName -- atomic formulas
    | Not Formula
    | And Formula Formula
    | Or Formula Formula
    | Implies Formula Formula
    | Iff Formula Formula
    deriving (Eq, Show)
```

We introduce a binary operator syntax:

```haskell id=ac0b9ead-3474-4ec5-a257-7fb4e95166b1
infixr 8 /\, ∧
(/\) = And
(∧) = And -- input with "\and"

infixr 5 \/, ∨, ==>
(\/) = Or
(∨) = Or -- input with "\or"
(==>) = Implies

infixr 4 <==>, ⇔
(<==>) = Iff
(⇔) = Iff -- input with "\lr"
```

Example formulas:

```haskell id=1e080563-59f5-46b1-bbd0-e61cd07b8628
p, q, r, s, t :: Formula

p = Prop "p"
q = Prop "q"
r = Prop "r"
s = Prop "s"
t = Prop "t"

satisfiable_formulas = [
    p ∧ q ∧ s ∧ p,
    T,
    p,
    Not p,
    (p ∨ q ∧ r) ∧ (Not p ∨ Not r),
    (p ∨ q) ∧ (Not p ∨ Not q)
  ]

unsatisfiable_formulas = [
    p ∧ q ∧ s ∧ Not p,
    T ∧ F,
    F,
    (p ∨ q ∧ r) ∧ Not p ∧ Not r,
    (p ⇔ q) ∧ (q ⇔ r) ∧ (r ⇔ s) ∧ (s ⇔ Not p)
  ]
```

## Random generation of propositional formulas (for testing)

```haskell id=3f91ea34-337e-42d6-b41d-ea8efa8e7ff8
instance Arbitrary Formula where
    arbitrary = sized f where
      
      f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]

      f size = frequency [
        (1, liftM Not (f (size - 1))),
        (4, do
              size' <- choose (0, size - 1)
              conn <- oneof $ map return [And, Or, Implies, Iff]
              left <- f size'
              right <- f $ size - size' - 1
              return $ conn left right)
        ]
```

# Semantics (EXERCISE)

Define the semantic function for propositional logic. *Hint*: proceed by structural induction on formulas (ignoring the cases corresponding to quantifiers and relations of >0 arity).

```haskell id=87b68bb2-c37e-40b8-b295-1afb1c6ef170
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
eval (Iff φ ψ) ρ = (eval φ ρ) == (eval ψ ρ)
eval _ _ = error "not a propositional formula"
```

Tests for the evaluation function:

```haskell id=1a2f850b-8bbe-4377-8643-088a7965d8cf
ρ0 = const True
ρ1 = const False
ρ2 = update ρ0 "p" False

test_eval =
  eval (p ∧ Not p) ρ0 == False &&
  eval (p ∧ Not p) ρ1 == False &&
  eval (p ∨ q) ρ2 == True

quickCheck test_eval
```

## Satisfiable formulas

List of variables appearing in a formula:

```haskell id=12912ddf-4523-414b-88c9-d89cfc1911f9
variables :: Formula -> [PropName]
variables = nub . go where
  go T = []
  go F = []
  go (Prop p) = [p]
  go (Not φ) = go φ
  go (And φ ψ) = go φ ++ go ψ
  go (Or φ ψ) = go φ ++ go ψ
  go (Implies φ ψ) = go φ ++ go ψ
  go (Iff φ ψ) = go φ ++ go ψ
  go _ = error "not a propositional formula"
```

A trivial SAT solver based on truth tables:

```haskell id=bea5931e-fa18-408f-9445-2c3fa34fa4d3
type SATSolver = Formula -> Bool

-- the list of all valuations on a given list of variables
valuations :: [PropName] -> [Valuation]
valuations [] = [undefined]
valuations (x : xs) = concat [[update ρ x True, update ρ x False] | ρ <- valuations xs]

satisfiable :: SATSolver
satisfiable φ = or [eval φ ρ | ρ <- valuations (variables φ)]
```

## Tautologies (EXERCISE)

Write a program that checks whether a given input formula is a tautology. *Hint*: Reduce to satisfiability.

```haskell id=db25be31-3575-4d17-8505-9ccb16374dc6
tautology :: Formula -> Bool
tautology φ = and [eval φ ρ | ρ <- valuations (variables φ)]
```

# Normal forms

## Negation normal form (EXERCISE)

A formula of propositional logic is in *negation normal form* (NNF) if the only connectives are true (T), false (F), conjunction (And), disjunction (Or), and negation (Not), and moreover negation is only applied to atomic formulas:

```haskell id=93be2d3c-9954-43e0-80d7-605f24510083
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

quickCheck $
  is_nnf (Not p ∧ (q ∨ (r ∧ s)))  -- NNF example
  && (not $ is_nnf $ Not (p ∨ q)) -- NNF non-example
```

Write a function that turns an arbitrary formula to a *logically equivalent* one in NNF. What is the complexity of the NNF translation? *Hint*: Proceed by structural induction on formulas:

1. express Implies in terms of Not and Or,
2. express Iff in terms of And, Or, and Not, and
3. push negation inside the formula with De Morgan's laws.

```haskell id=3576f906-07d6-4ee3-a45b-761fdee23d71
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
```

Tests:

```haskell id=44423d5c-77b4-47cc-a213-732fa59bfeb5
prop_nnf :: Formula -> Bool
prop_nnf φ = let ψ = nnf φ in is_nnf ψ && (tautology $ φ ⇔ ψ)

quickCheck prop_nnf
```

## Disjunctive normal form (EXERCISE)

A *literal* is either  a propositional variable, or the negation of a propositional variable:

```haskell id=3686f71d-5dc7-4628-82c1-ab120d567346
data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p
```

A *clause* is a conjunction of literals. A formula of propositional logic is in *disjunctive normal form* (DNF) if it is a disjunction of clauses. It is customary to represent DNF formulas as lists of lists of literals:

```haskell id=03676d3f-58ba-487c-8f34-a24baeea68ac
type DNFClause = [Literal]
type DNF = [DNFClause]

dnf2formula :: [[Literal]] -> Formula
dnf2formula [] = F
dnf2formula lss = foldr1 Or (map go lss) where
  go [] = T
  go ls = foldr1 And (map go2 ls)
  go2 (Pos p) = Prop p
  go2 (Neg p) = Not (Prop p)
```

Write a function that turns an arbitrary formula to a *logically equivalent* one in DNF. What is the complexity of the DNF translation? *Hint*: Convert the formula to NNF first, then proceed by structural induction on NNF formulas (analogy with polynomial multiplication).

```haskell id=a5597fc2-b1fe-423a-9baa-9f46132a229f
dnfHelper :: Formula -> DNF
dnfHelper T = [[]]
dnfHelper F = []
dnfHelper (Prop propName) = [ [Pos propName] ]
dnfHelper (Not (Prop propName)) = [ [Neg propName] ]
dnfHelper (And phi psi) = let a = dnfHelper phi in let b = dnfHelper psi in
  map (\[x,y] -> x ++ y) (sequence [a, b])
dnfHelper (Or phi psi) = dnfHelper phi ++ dnfHelper psi
dnfHelper _ = error "not a valid nnf formula"

dnf :: Formula -> DNF
dnf phi = let n = nnf phi in
  dnfHelper n
```

Tests:

```haskell id=3efc25df-2155-48e6-9f59-57795ac1f3cc
test_dnf :: Formula -> Bool
test_dnf φ = tautology $ φ ⇔ (dnf2formula (dnf φ))

quickCheckWith (stdArgs {maxSize = 18}) test_dnf
```

## Conjunctive normal form

The *conjunctive normal form* (CNF) is entirely dual to the DNF. In the next lab we will see how to convert a propositional formula to an *equisatisfiable* one in CNF, which is sufficient for SAT solving.

# DNF-based SAT solver (EXERCISE)

Write a SAT solver based on the following recipe:

1. Convert the input formula to DNF.
2. Find whether there exists a satisfiable clause.

*Hint*: A clause is satisfiable iff it does not contain the same literal both positively and negatively.

What is the complexity of this SAT solver compared to the one based on truth tables? Is it potentially more efficient on satisfiable or on unsatisfiable instances?

```haskell id=11006d5e-00ba-4f89-84e9-2c5e70a6c465
sat_dnf :: SATSolver
sat_dnf input_formula =
  let dnf_instance = dnf input_formula
      formula_from_dnf = dnf2formula dnf_instance
  in satisfiable formula_from_dnf
```

Tests:

```haskell id=fd12e470-ef51-4212-b0bd-365c83f3c9d9
prop_sat_dnf :: Formula -> Bool
prop_sat_dnf phi = sat_dnf phi == satisfiable phi

quickCheckWith (stdArgs {maxSize = 20}) prop_sat_dnf

test_solver :: SATSolver -> Bool
test_solver solver = and $ map solver satisfiable_formulas ++ map (not . solver) unsatisfiable_formulas

quickCheck (test_solver sat_dnf)
```

```bash id=7f1782ce-04b7-466f-a473-7f10539dcc13
stack install QuickCheck
```

<details id="com.nextjournal.article">
<summary>This notebook was exported from <a href="https://nextjournal.com/a/NfKvDwhdLnxzGa4jct3yT?change-id=Cto6m5LbDsFq83vHwTkeNC">https://nextjournal.com/a/NfKvDwhdLnxzGa4jct3yT?change-id=Cto6m5LbDsFq83vHwTkeNC</a></summary>

```edn nextjournal-metadata
{:article
 {:nodes
  {"03676d3f-58ba-487c-8f34-a24baeea68ac"
   {:compute-ref #uuid "ed2ab702-c3e7-4534-b1ca-b837a2e02ccb",
    :exec-duration 380,
    :id "03676d3f-58ba-487c-8f34-a24baeea68ac",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "0f647ad7-4c90-4771-a1d2-7790f11b7182"
   {:environment
    [:environment
     {:article/nextjournal.id
      #uuid "02b6fac0-b81e-4de7-bc28-418ca38429b2",
      :node/id "3db667a5-ee2a-4dac-a876-8d1e8fce2b48",
      :change/nextjournal.id
      #uuid "5d460bfe-8716-4272-858b-d87c1a368ed1"}],
    :environment? true,
    :id "0f647ad7-4c90-4771-a1d2-7790f11b7182",
    :kind "runtime",
    :language "bash",
    :name "Haskell+QuickCheck",
    :resources {:machine-type "n1-standard-2"},
    :type :nextjournal,
    :docker/environment-image
    "docker.nextjournal.com/environment@sha256:33e47b045c71dc80ec10b72dbf586cf6a9ebf308bb60bacd81159f1b41d1c33f"},
   "11006d5e-00ba-4f89-84e9-2c5e70a6c465"
   {:compute-ref #uuid "66d79dd7-0ceb-4de2-b997-e9bc4eaede2c",
    :exec-duration 201,
    :id "11006d5e-00ba-4f89-84e9-2c5e70a6c465",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "12912ddf-4523-414b-88c9-d89cfc1911f9"
   {:compute-ref #uuid "e2b286af-ad83-4694-8649-ecdc41d97e6d",
    :exec-duration 484,
    :id "12912ddf-4523-414b-88c9-d89cfc1911f9",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "1a2f850b-8bbe-4377-8643-088a7965d8cf"
   {:compute-ref #uuid "b5150645-9afa-4e11-b38c-df4e9e4bb9f1",
    :exec-duration 529,
    :id "1a2f850b-8bbe-4377-8643-088a7965d8cf",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "1e080563-59f5-46b1-bbd0-e61cd07b8628"
   {:compute-ref #uuid "30cc488f-ff15-49fd-b5b5-6af44e0b960f",
    :exec-duration 329,
    :id "1e080563-59f5-46b1-bbd0-e61cd07b8628",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "3576f906-07d6-4ee3-a45b-761fdee23d71"
   {:compute-ref #uuid "f4815abd-a061-4b60-aeef-d07626dc3045",
    :exec-duration 380,
    :id "3576f906-07d6-4ee3-a45b-761fdee23d71",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "3686f71d-5dc7-4628-82c1-ab120d567346"
   {:compute-ref #uuid "371327a0-1204-4eb1-8f7f-e442519ffbd5",
    :exec-duration 382,
    :id "3686f71d-5dc7-4628-82c1-ab120d567346",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "3efc25df-2155-48e6-9f59-57795ac1f3cc"
   {:compute-ref #uuid "2fbf2f38-be53-43a4-b713-2a710d55f850",
    :exec-duration 94886,
    :id "3efc25df-2155-48e6-9f59-57795ac1f3cc",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "3f91ea34-337e-42d6-b41d-ea8efa8e7ff8"
   {:compute-ref #uuid "d483697d-437d-43a6-be8d-98c19b1ac47e",
    :exec-duration 1154,
    :id "3f91ea34-337e-42d6-b41d-ea8efa8e7ff8",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "44423d5c-77b4-47cc-a213-732fa59bfeb5"
   {:compute-ref #uuid "dce0ae7f-4367-4c78-8a81-d8f36de7ca86",
    :exec-duration 718,
    :id "44423d5c-77b4-47cc-a213-732fa59bfeb5",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "573eb208-5c0a-4964-beed-5a54dbc80ee1"
   {:compute-ref #uuid "8ed02193-b343-454c-a1a0-9fd82ea156ba",
    :exec-duration 446,
    :id "573eb208-5c0a-4964-beed-5a54dbc80ee1",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "64937988-5a01-4873-b337-1d6159c293b7"
   {:compute-ref #uuid "e8d9c2fb-f329-4cd8-8041-54234d807ab3",
    :exec-duration 2463,
    :id "64937988-5a01-4873-b337-1d6159c293b7",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"],
    :runtime-language [:node "b46294cd-64fb-45c5-b019-7ba2297c77e3"]},
   "7f1782ce-04b7-466f-a473-7f10539dcc13"
   {:compute-ref #uuid "56c20701-cfd8-4611-b8bf-5a9e3a8b5ea2",
    :exec-duration 4870,
    :id "7f1782ce-04b7-466f-a473-7f10539dcc13",
    :kind "code",
    :locked? true,
    :output-log-lines {},
    :runtime [:runtime "0f647ad7-4c90-4771-a1d2-7790f11b7182"],
    :stdout-collapsed? true},
   "87b68bb2-c37e-40b8-b295-1afb1c6ef170"
   {:compute-ref #uuid "5f87ad65-deff-4f5f-9e49-f14ee98705e8",
    :exec-duration 398,
    :id "87b68bb2-c37e-40b8-b295-1afb1c6ef170",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "93be2d3c-9954-43e0-80d7-605f24510083"
   {:compute-ref #uuid "d5ed4120-2697-4ad0-af0e-a5f7a4157438",
    :exec-duration 644,
    :id "93be2d3c-9954-43e0-80d7-605f24510083",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "a5597fc2-b1fe-423a-9baa-9f46132a229f"
   {:compute-ref #uuid "15b78805-064b-4033-bcea-282c85477c5d",
    :exec-duration 327,
    :id "a5597fc2-b1fe-423a-9baa-9f46132a229f",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "ac0b9ead-3474-4ec5-a257-7fb4e95166b1"
   {:compute-ref #uuid "d5380d3b-3462-406f-8e4c-80b3f5b88b0f",
    :exec-duration 345,
    :id "ac0b9ead-3474-4ec5-a257-7fb4e95166b1",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "b46294cd-64fb-45c5-b019-7ba2297c77e3"
   {:environment
    [:environment
     {:article/nextjournal.id
      #uuid "02b6fac0-b81e-4de7-bc28-418ca38429b2",
      :change/nextjournal.id
      #uuid "5d460bfe-8716-4272-858b-d87c1a368ed1",
      :node/id "3db667a5-ee2a-4dac-a876-8d1e8fce2b48"}],
    :id "b46294cd-64fb-45c5-b019-7ba2297c77e3",
    :kernelspec
    {:display_name "Haskell",
     :argv
     ["/opt/stack/bin/ihaskell"
      "kernel"
      "{connection_file}"
      "--debug"
      "--ghclib"
      "/opt/stack/programs/x86_64-linux/ghc-8.6.5/lib/ghc-8.6.5"
      "+RTS"
      "-M3g"
      "-N2"
      "-RTS"
      "--stack"],
     :language "haskell"},
    :kind "runtime-language"},
   "b62929ed-f789-40e2-9c21-658379ab2182"
   {:environment [:environment "0f647ad7-4c90-4771-a1d2-7790f11b7182"],
    :id "b62929ed-f789-40e2-9c21-658379ab2182",
    :kind "runtime",
    :language "haskell",
    :type :jupyter,
    :jupyter/kernelspec
    {:display_name "Haskell",
     :argv
     ["/opt/stack/bin/ihaskell"
      "kernel"
      "{connection_file}"
      "--debug"
      "--ghclib"
      "/opt/stack/programs/x86_64-linux/ghc-8.6.5/lib/ghc-8.6.5"
      "+RTS"
      "-M3g"
      "-N2"
      "-RTS"
      "--stack"],
     :language "haskell"}},
   "bea5931e-fa18-408f-9445-2c3fa34fa4d3"
   {:compute-ref #uuid "c7adb948-5657-45a0-ba76-8aac9cba0b5f",
    :exec-duration 314,
    :id "bea5931e-fa18-408f-9445-2c3fa34fa4d3",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "db25be31-3575-4d17-8505-9ccb16374dc6"
   {:compute-ref #uuid "100b8a8e-cf34-4a6e-a012-e48b4cfe3168",
    :exec-duration 346,
    :id "db25be31-3575-4d17-8505-9ccb16374dc6",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]},
   "fd12e470-ef51-4212-b0bd-365c83f3c9d9"
   {:compute-ref #uuid "d700ceb5-c3f5-4fc4-b7f1-793293369346",
    :exec-duration 17604,
    :id "fd12e470-ef51-4212-b0bd-365c83f3c9d9",
    :kind "code",
    :output-log-lines {},
    :runtime [:runtime "b62929ed-f789-40e2-9c21-658379ab2182"]}},
  :nextjournal/id #uuid "03063d0e-ef56-4b14-8e3f-effd5f276cba",
  :article/change
  {:nextjournal/id #uuid "604fde03-54d6-40ec-8c2f-2249ae7eab99"}}}

```
</details>
