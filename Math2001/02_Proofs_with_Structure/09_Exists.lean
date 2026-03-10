/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.Parity

math2001_init

/-!
# Quantificateur existenciel

**Rappel**: vous pouvez trouver la liste des lemmes vus en cours dans le fichier `lemmes.lean`.
-/

example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra
  done

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers
  done

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra
  done

/-!
## Exercices
-/

example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  sorry
  done

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  sorry
  done

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  sorry
  done

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry
  done

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  sorry
  done

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  sorry
  done

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  sorry
  done

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry
  done

-- Plus compliqué : allez d'abord commencer la feuill 10

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry
  done

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
  done
