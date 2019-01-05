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

  plus : (n : Nat) -> (m : Nat) -> Nat
  plus Z m = m
  plus (S k) m = S (Basics.Playground2.plus k m)


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
