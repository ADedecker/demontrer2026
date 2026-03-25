/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Mathlib.Tactic.ByContra

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  by_contra' h
  have H : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at H
  done

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  by_contra' h1
  obtain ⟨hx, hy⟩ := h1
  have H : (0 : ℝ) > 0 :=
    calc
      0 = x + y := by rw [h]
      _ > 0 := by extra
  numbers at H
  done



/-! # Exercises -/

-- `lemma not_lt_of_ge {a b : ℝ} (h : a ≥ b) : ¬a < b`

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  by_contra' h
  obtain ⟨ t, ht1, ht2 ⟩ := h
  have hh : ¬ (t < 5) := by
    apply not_lt_of_ge
    rel [ht2]
  have hhh : t < 5 := by
    calc t ≤ 4 := by rel [ht1]
      _    < 5 := by numbers
  contradiction
  done

  -- `lemma abs_le_of_sq_le_sq' {a b : ℝ} (h1 : a ^ 2 ≤ b ^ 2) (h2 : 0 ≤ b) : -b ≤ a ∧ a ≤ b`

example {x : ℝ} (hx : x ^ 2 < 9) : x < 3 ∧ x > -3 := by
  have hx' : x^2 < 3^2 := by
    calc x^2 < 9 := by rel [hx]
      _      = 3^2 := by numbers
  have H : -3 < x ∧ x < 3 := by
    apply abs_lt_of_sq_lt_sq' hx'
    numbers
  obtain ⟨h1 , h2⟩ := H
  constructor
  · rel [h2]
  · rel [h1]
  done

-- `lemma le_or_succ_le {n a : ℤ} : n ≤ a ∨ a+1 ≤ n`

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  by_contra' h
  obtain ⟨ n , hn ⟩ := h
  have H : n ≤ 1 ∨ 2 ≤ n := by apply le_or_succ_le n 1
  obtain H | H := H
  · have hn1 : n^2 ≤ 1 := by
      calc n^2 ≤ 1^2 := by rel [H]
        _ = 1 := by numbers
    have hn2 : ¬ (n^2 = 2) := by
      apply ne_of_lt
      calc n^2 ≤ 1 := by rel [hn1]
        _      < 2 := by numbers
    contradiction
  · have hn1 : n^2 ≥ 4 := by
      calc n^2 ≥ 2^2 := by rel [H]
        _ = 4 := by numbers
    have hn2 : ¬ (n^2 = 2) := by
      apply ne_of_gt
      calc n^2 ≥ 4 := by rel [hn1]
        _      > 2 := by numbers
    contradiction
  done
