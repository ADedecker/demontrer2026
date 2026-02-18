/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
# Le connecteur "ou"
-/

-- le_or_succ_le {n a : ℤ} : n ≤ a ∨ a+1 ≤ n

-- eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℝ}  (h : a * b = 0) : a = 0 ∨ b = 0

-- ne_of_lt {a b : ℝ} (h : a < b) : a ≠ b
-- ne_of_gt {a b : ℝ} (h : a > b) : a ≠ b

-- Montrer un "ou" : `right` et `left`
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers
  done

-- Utiliser un "ou" : `obtain`
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  · calc
      x * y + x = 1 * y + 1 := by rw [hx]
      _ = y + 1 := by ring
  · calc
      x * y + x = x * -1 + x := by rw [hy]
      _ = -1 + 1 := by ring
      _ = y + 1 := by rw [hy]
  done

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 : (x - 1) * (x - 2) = 0 := by
    calc
      (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
      _ = 0 := by rw [hx]
  have h2 : x - 1 = 0 ∨ x - 2 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero
    apply h1
  /- Variantes:
  `have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1`
  ou
  `apply eq_zero_or_eq_zero_of_mul_eq_zero at h1`
  -/
  obtain h3 | h4 := h2
  · left
    addarith [h3]
  · right
    addarith [h4]
  done

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn : n ≤ 1 ∨ 2 ≤ n := by
    apply le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · sorry
  done

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  sorry
  done

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  sorry
  done

example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  sorry
  done

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  sorry
  done

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  sorry
  done

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  sorry
  done

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  sorry
  done

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry
  done

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) :
    a = b ∨ a = 2 * b := by
  sorry
  done

-- Pour l'exercice suivant, vous pouvez (ou pas) utiliser le lemme :
-- pow_eq_zero {x : ℝ} {n : ℕ} (H : x ^ n = 0) : x = 0

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry
  done

example {n : ℕ} : n ^ 2 ≠ 7 := by
  sorry
  done

example {x : ℤ} : 2 * x ≠ 3 := by
  sorry
  done

example {t : ℤ} : 5 * t ≠ 18 := by
  sorry
  done

example {n : ℤ} : n ^ 2 ≠ 2 := by
  sorry
  done

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
  done
