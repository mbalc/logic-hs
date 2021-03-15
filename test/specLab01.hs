module Main where

import Lab01
import Test.QuickCheck

{-# ANN module "HLint: ignore Use camelCase" #-}

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


p, q, r, s, t :: Formula
p = Prop "p"

q = Prop "q"

r = Prop "r"

s = Prop "s"

t = Prop "t"

instance Arbitrary Formula where
  arbitrary = sized f
    where
      f 0 = oneof $ map return $ [p, q, r, s, t] ++ [T, F]
      f size =
        frequency
          [ (1, fmap Not (f (size - 1)))
          , ( 4
            , do size' <- choose (0, size - 1)
                 conn <- oneof $ map return [And, Or, Implies, Iff]
                 left <- f size'
                 right <- f $ size - size' - 1
                 return $ conn left right)
          ]


satisfiable_formulas =
  [ p ∧ q ∧ s ∧ p
  , T
  , p
  , Not p
  , (p ∨ q ∧ r) ∧ (Not p ∨ Not r)
  , (p ∨ q) ∧ (Not p ∨ Not q)
  ]

unsatisfiable_formulas =
  [ p ∧ q ∧ s ∧ Not p
  , T ∧ F
  , F
  , (p ∨ q ∧ r) ∧ Not p ∧ Not r
  , (p ⇔ q) ∧ (q ⇔ r) ∧ (r ⇔ s) ∧ (s ⇔ Not p)
  ]


-- test
ρ0 = const True

ρ1 = const False

ρ2 = update ρ0 "p" False

test_eval =
  not (eval (p ∧ Not p) ρ0) && not (eval (p ∧ Not p) ρ1) && eval (p ∨ q) ρ2

test1 = quickCheck test_eval


test2 =
  quickCheck $ is_nnf (Not p ∧ (q ∨ (r ∧ s))) && not (is_nnf $ Not (p ∨ q))


prop_nnf :: Formula -> Bool
prop_nnf φ =
  let ψ = nnf φ
  in is_nnf ψ && tautology (φ ⇔ ψ)

test3 = quickCheck prop_nnf


test_dnf :: Formula -> Bool
test_dnf φ = tautology $ φ ⇔ dnf2formula (dnf φ)

test4 = quickCheckWith (stdArgs {maxSize = 18}) test_dnf

test5 = quickCheckWith (stdArgs {maxSize = 20}) prop_sat_dnf

test_solver :: SATSolver -> Bool
test_solver solver = and $ map solver satisfiable_formulas ++ map (not . solver) unsatisfiable_formulas

test6 = quickCheck (test_solver sat_dnf)


main :: IO ()
main = do
    test1
    test2
    test3
    test4
    test5
    test6
