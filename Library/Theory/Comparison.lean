/- Copyright (c) Mario Carneiro, 2023. -/
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Nat.Order.Lemmas

macro "le_or_succ_le" a:term:arg n:num  : term =>
  `(show $a ≤ $n ∨ $(Lean.quote (n.getNat+1)) ≤ $a from le_or_lt ..)
