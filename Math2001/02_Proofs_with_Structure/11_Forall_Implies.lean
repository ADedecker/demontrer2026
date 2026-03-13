/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.Parity

math2001_init

namespace Int

/-!
# Implication et quantificateur universel
-/

example : ∀ n : ℤ, Odd (4 * n + 1) := by
  intro n
  dsimp [Odd]
  use 2 * n
  ring
  done

example (x : ℝ) (hx : ∀ y : ℝ, x ≤ y ^ 2) : x ≤ 0 := by
  calc
    x ≤ 0 ^ 2 := by apply hx
    _ = 0 := by ring
  done

example (n : ℤ) : Even n → Even (n ^ 2) := by
  intro hn
  dsimp [Even]
  dsimp [Even] at hn
  obtain ⟨k, hk⟩ := hn
  use 2 * k^2
  rw [hk]
  ring
  done

example {x : ℝ} (h : x < 0 → x = -1) (h2 : 2 * x + 1 ≤ 0) :
    x = -1 := by
  apply h
  calc
    x = (2 * x) / 2 := by ring
    _ < (2 * x) / 2 + 1 / 2 := by extra
    _ = (2 * x + 1) / 2 := by ring
    _ ≤ 0 / 2 := by rel [h2]
    _ = 0 := by ring
  done

/-!
## Exercices
-/

example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 := by
  sorry
  done

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  sorry
  done

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry
  done

example : ∀ n m : ℤ, Even n → Even (n * m) := by
  sorry
  done

example : ∀ n m : ℤ, Even n → Odd m → Odd (n + m) := by
  sorry
  done

example {a b : ℝ} (h : ∀ x, x ≤ a → x ≤ b) : a ≤ b := by
  sorry
  done

example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  sorry
  done

example : ∀ x y : ℝ, x + 4 = y + 4 → x = y := by
  sorry
  done

example : ∀ x y : ℚ, 2 * x - 35 = 2 * y - 35 → x = y := by
  sorry
  done

example : ∀ x : ℚ, ∃ y : ℚ, x = (-3) * y := by
  sorry
  done

/-
Les exercices suivants sont plus difficiles, allez d'abord faire la feuille 12
-/

example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  sorry
  done

example : ∃ (k : ℤ), ∀ n ≥ k, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  sorry
  done

example : ∃ (k : ℝ), ∀ x ≥ k, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  sorry
  done

example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  sorry
  done
