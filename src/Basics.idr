||| Basics: Functional Programming in Idris
module Basics
%access public export

namespace Days
  ||| Days of week.
  data Day = ||| `Monday` is a `Day`.
             Monday
           | ||| `Tuesday` is a `Day`.
             Tuesday
           | ||| `Wednesday` is a `Day`.
             Wednesday
           | ||| `Thursday` is a `Day`.
             Thursday
           | ||| `Friday` is a `Day`.
             Friday
           | ||| `Saturday` is a `Day`.
             Saturday
           | ||| `Sunday` is ad `Day`.
             Sunday

  %name Day day, day1, day2

  ||| Determine the next weekday after a day.
  nextWeekday : Day -> Day
  nextWeekday Monday = Tuesday
  nextWeekday Tuesday = Wednesday
  nextWeekday Wednesday = Thursday
  nextWeekday Thursday = Friday
  nextWeekday Friday = Saturday
  nextWeekday Saturday = Sunday
  nextWeekday Sunday = Monday



  ||| The second weekday after `Saturday` is `Monday`
  testNextWeekday : (nextWeekday (nextWeekday Saturday)) = Monday
  testNextWeekday = Refl

namespace Booleans
  -- ||| Boolean Data Type
  -- data Bool = True | False
  -- data Bool : Type where
  --      True : Bool
  --     False : Bool

  -- not : (b : Bool) -> Bool
  -- not True = False
  -- not False = True

  andb : (b1 : Bool) -> (b2 : Bool) -> Bool
  andb True b2 = b2
  andb False b2 = False

  orb : (b1 : Bool) -> (b2 : Bool) -> Bool
  orb True b2 = True
  orb False b2 = b2

  testOrb1 : (orb True False) = True
  testOrb1 = Refl

  testOrb2 : (orb False False) = False
  testOrb2 = Refl

  testOrb3 : (orb False True) = True
  testOrb3 = Refl

  testOrb4 : (orb True True) = True
  testOrb4 = Refl

  -- infixl 4 &&, ||
  -- (&&) : Bool -> Bool -> Bool
  -- (&&) = andb

  -- (||) : Bool -> Bool -> Bool
  -- (||) = orb

  testOrb5 : False || False || True = True
  testOrb5 = Refl

  -- BasicsExc.ExcNandb
  -- BasicsExc.ExcAndb3

namespace Numbers

  -- data Nat : Type where
  --        Z : Nat
  --        S : Nat -> Nat

  -- %name Nat k, n, m, l

  pred : (n : Nat) -> Nat
  pred  Z    = Z
  pred (S k) = k


  minusTwo : (n : Nat)  -> Nat
  minusTwo Z         = Z
  minusTwo (S Z)     = Z
  minusTwo (S (S k)) = k

  evenb : (n : Nat) -> Bool
  evenb Z         = True
  evenb (S Z)     = False
  evenb (S (S k)) = evenb k

  oddb : (n : Nat) -> Bool
  oddb n = not (evenb n)

  testOddb1 : oddb 1 = True
  testOddb1 = Refl


  testOddb2 : oddb 4 = False
  testOddb2 = Refl

namespace Playground2

--   plus : (n : Nat) -> (m : Nat) -> Nat
--   plus Z m = m
--   plus (S k) m = S (Basics.Playground2.plus k m)


  -- mult : (n, m : Nat) -> Nat
  -- mult  Z    _ = Z
  -- mult (S k) m = plus m (mult k m)

  -- testMult1 : (mult 3 3) = 9
  -- testMult1 = Refl

  -- minus : (n, m : Nat) -> Nat
  -- minus Z _ = Z
  -- minus n Z = n
  -- minus (S k) (S j) = minus k j

  exp : (base, power : Nat) -> Nat
  exp base Z = S Z
  exp base (S p) = mult base (exp base p)

  -- BasicsExc.ExcFactorial

  -- syntax [x] "+" [y] = plus  x y
  -- syntax [x] "-" [y] = minus x y
  -- syntax [x] "*" [y] = mult  x y

  -- ||| Test natural numbers for equality.
  -- (==) : (n, m : Nat) -> Bool
  -- (==) Z       Z   = True
  -- (==) Z     (S j) = False
  -- (==) (S k)  Z    = False
  -- (==) (S k) (S j) = (== k j)


  -- ||| Test whether a number is less than or equal to another.
  -- lte : (n, m : Nat) -> Bool
  -- lte  Z     m    = True
  -- lte  n     Z    = False
  -- lte (S k) (S j) = lte k j

  testLte1 : lte 2 2 = True
  testLte1 = Refl

  testLte2 : lte 2 4 = True
  testLte2 = Refl


  testLte3 : lte 4 2 = False
  testLte3 = Refl

  -- BasicsExc.ExcBltNat

  plus_Z_n : (n : Nat) -> 0 + n = n
  plus_Z_n _ = Refl

  plus_1_l : (n : Nat) -> 1 + n = S n
  plus_1_l _ = Refl

  mult_0_l : (n : Nat) -> 0 * n = 0
  mult_0_l _ = Refl

  -- plus_n_Z : (n: Nat) -> n = n + 0
  -- plus_n_Z n = Refl

  plus_id_example : (n, m: Nat) -> (n = m) -> n + n = m + m
  plus_id_example n m prf = rewrite prf in Refl

  -- BasicsExc.ExcPlusIdExercise

  mult_0_plus : (n, m : Nat) -> (0 + n) * m = n * (0 + m)
  mult_0_plus n m = Refl

  -- BasicsExc.ExcMultS1

  -- plus_1_neq_0_firsttry : (n :Nat) -> (n + 1) == 0 = False
  -- plus_1_neq_0_firsttry n = Refl

  plus_1_neq_0 : (n: Nat) -> (n + 1) == 0 = False
  plus_1_neq_0 Z = Refl
  plus_1_neq_0 (S k) = Refl

  ||| a proof that boolean netation is involutive
  not_involutive : (b : Bool) -> not (not b) = b
  not_involutive False = Refl
  not_involutive True = Refl

  andb_commutative : (b, c : Bool) -> b && c = c && b
  andb_commutative False False = Refl
  andb_commutative False True = Refl
  andb_commutative True False = Refl
  andb_commutative True True = Refl

  andb_commutative'_rhs_1 : (c : Bool) -> False = (c && (Delay False))
  andb_commutative'_rhs_1 False = Refl
  andb_commutative'_rhs_1 True = Refl

  andb_commutative'_rhs_2 : (c : Bool) -> c = (c && (Delay True))
  andb_commutative'_rhs_2 False = Refl
  andb_commutative'_rhs_2 True = Refl

  andb_commutative' : (b, c : Bool) -> b && c = c && b
  andb_commutative' False = andb_commutative'_rhs_1
  andb_commutative' True = andb_commutative'_rhs_2

  -- BasicExc.AndbTrueElim2

  -- BasicExc.ZeroNbeqPlus1

  -- BasicExc.BooleanFunctions

  -- BasicExc.AndbEqOrb

  -- BasicExc.Binary
