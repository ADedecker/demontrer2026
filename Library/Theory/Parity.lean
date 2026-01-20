/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.IntervalCases
import Library.Theory.Division

def Int.IsEven (n : ℤ) : Prop :=
  ∃ k, n = 2 * k

def Int.IsOdd (n : ℤ) : Prop :=
  ∃ k, n = 2 * k + 1

theorem Int.isEven_or_isOdd (n : ℤ) : Int.IsEven n ∨ Int.IsOdd n := by
  obtain ⟨q, r, h, h', hn⟩ := n.exists_quotient_remainder 2 (by norm_num1)
  refine' exists_or.mp ⟨q, _⟩
  interval_cases r <;> simp [hn]

theorem Int.isOdd_iff_not_isEven (n : ℤ) : IsOdd n ↔ ¬ IsEven n := by
  constructor
  · intro ⟨k, hk⟩ ⟨l, hl⟩
    have : (2:ℤ) ∣ 1 := ⟨l - k, by linear_combination hl - hk⟩
    have : ¬ ((2:ℤ) ∣ 1) := by decide
    contradiction
  · intro h
    obtain h1 | h2 := Int.isEven_or_isOdd n
    · contradiction
    · apply h2

theorem Int.isEven_iff_not_isOdd (n : ℤ) : IsEven n ↔ ¬ IsOdd n := by
  constructor
  · intro ⟨k, hk⟩ ⟨l, hl⟩
    have : (2:ℤ) ∣ 1 := ⟨k - l, by linear_combination hk - hl⟩
    have : ¬ ((2:ℤ) ∣ 1) := by decide
    contradiction
  · intro h
    obtain h1 | h2 := Int.isEven_or_isOdd n
    · apply h1
    · contradiction

def Nat.IsEven (n : ℕ) : Prop :=
  ∃ k, n = 2 * k

def Nat.IsOdd (n : ℕ) : Prop :=
  ∃ k, n = 2 * k + 1

theorem Nat.isEven_or_isOdd (n : ℕ) : Nat.IsEven n ∨ Nat.IsOdd n := by
  obtain ⟨q, r, h, hn⟩ := n.exists_quotient_remainder 2 (by norm_num1)
  refine' exists_or.mp ⟨q, _⟩
  interval_cases r <;> simp [hn]

theorem Nat.isOdd_iff_not_isEven (n : ℕ) : IsOdd n ↔ ¬ IsEven n := by
  constructor
  · intro ⟨k, hk⟩ ⟨l, hl⟩
    zify at hk hl
    have : (2:ℤ) ∣ 1 := ⟨l - k, by linear_combination hl - hk⟩
    have : ¬ ((2:ℤ) ∣ 1) := by decide
    contradiction
  · intro h
    obtain h1 | h2 := Nat.isEven_or_isOdd n
    · contradiction
    · apply h2

theorem Nat.isEven_iff_not_isOdd (n : ℕ) : IsEven n ↔ ¬ IsOdd n := by
  constructor
  · intro ⟨k, hk⟩ ⟨l, hl⟩
    zify at hk hl
    have : (2:ℤ) ∣ 1 := ⟨k - l, by linear_combination hk - hl⟩
    have : ¬ ((2:ℤ) ∣ 1) := by decide
    contradiction
  · intro h
    obtain h1 | h2 := Nat.isEven_or_isOdd n
    · apply h1
    · contradiction
