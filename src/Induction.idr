module Induction
import Basics
import Prelude.Interfaces
import Prelude.Nat

%access public export
%default total

plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z Z = Refl
plus_n_Z (S k) =
  let inductiveHypothesis = plus_n_Z k in
    rewrite inductiveHypothesis in Refl

minus_diag : (n : Nat) -> minus n n = 0
minus_diag Z = Refl
minus_diag (S k) = minus_diag k


-- InductionExc.BasicInduction
-- InductionExc.DoublePlus
-- InductionExc.EvenbS

mult_0_plus' : (n, m : Nat) -> (0 + n) * m = n * m
mult_0_plus' n m = Refl

-- plus_comm : (n, m : Nat) -> n + m = m + n

-- plus_rearrange : (n, m, p, q : Nat) ->
--                  (n + m) + (p + q) = (m + n) + (p +q)
-- plus_rearrange n m p q = rewrite plus_rearrange_lemma n m  in Refl
--   where
--   plus_rearrange_lemma : (n, m : Nat) -> n + m = m + n
--   plus_rearrange_lemma = plus_comm
