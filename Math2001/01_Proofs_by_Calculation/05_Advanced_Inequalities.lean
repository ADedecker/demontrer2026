/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {t : ℝ} (h1 : t * t = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  cancel t at h1
  addarith [h1]
  done

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 : t * t = 3 * t := by
    calc t * t = t ^ 2 := by ring
      _ = 3 * t := by rw [h1]
    done
  cancel t at h3
  addarith [h3]
  done


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 : a ^ 2 ≥ 1 ^ 2 := by
    calc
      a ^ 2 = b ^ 2 + 1 := by rw [h1]
      _ ≥ 1 := by extra
      _ = 1 ^ 2 := by ring
    done
  cancel 2 at h3
  done

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  sorry
  done

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  sorry
  done

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  sorry
  done

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  sorry
  done

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  sorry
  done
