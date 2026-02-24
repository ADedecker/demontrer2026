/- Copyright (c) Mario Carneiro, 2023. -/
import Mathlib.Init.Data.Int.Order
import Mathlib.Init.Data.Nat.Lemmas

macro "le_or_succ_le" a:term:arg n:num  : term =>
  `(show $a ≤ $n ∨ $(Lean.quote (n.getNat+1)) ≤ $a from le_or_lt ..)

protected lemma Nat.le_or_succ_le (n a : ℕ) : n ≤ a ∨ a+1 ≤ n := le_or_lt _ _

protected lemma Int.le_or_succ_le (n a : ℤ) : n ≤ a ∨ a+1 ≤ n := le_or_lt _ _
