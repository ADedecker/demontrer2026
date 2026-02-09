/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


-- lemma ne_of_lt (a b : ℝ ) (h : a < b) : a ≠ b

-- lemma ne_of_gt {a b : ℝ} (h : a > b) : a ≠ b

-- lemma le_antisymm {a b : ℝ} (h1 : a ≤ b) (h2 : b ≤ a) : a = b


-- introduction apply ?
example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers
  done

-- exo
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  extra
  done


example {t : ℝ} : t ^ 2 + 2 ≠ -(1/4) := by
  have ht : t^2 + 2 ≥ 0 := by extra
  apply ne_of_gt
  calc -(1/4) < 0 := by numbers
    _         ≤ t^2 + 2 := by rel [ht]
  done


example {t : ℝ} : t ^ 2 + 2 ≠ -(1/4) := by
  have ht : t^2 + 2 ≥ 0 := by extra
  apply ne_of_gt
  calc t^2 + 2 ≥ 0 := by rel [ht]
    _ > -(1/4) := by numbers
  done


example {x : ℝ} (hx : 4 * x + 2 = 1): x ≠ 0 := by
  have h : x = -(1/4) := by addarith [hx]
  apply ne_of_lt
  rw [h]
  numbers
  done


-- changer le nom des variables ?
-- ici on a deux sous preuve - on doit montrer indentation · etc
example {x y : ℝ} (h1 : x ^ 2 + y ^ 2 = 0) : x ^ 2 = 0 := by
  apply le_antisymm
  · calc
      x ^ 2 ≤ x ^ 2 + y ^ 2 := by extra
      _ = 0 := h1
  · extra
  done



example {x y : ℝ} (h1 : 2*x ≤ 2) (h2 : -3*x ≤ -3) : x = 1 := by
  apply le_antisymm
  · have h3 : 2*x ≤ 2*1 := by addarith [h1]
    cancel 2 at h3
  · have h4 : 3*1 ≤ 3*x := by addarith [h2]
    cancel 3 at h4
  done



/-! # Exercises -/

-- pas besoin de lemme
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  have h : m = 4 := by addarith [hm]
  rw [h]
  numbers
  done



example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  · calc s = (3*s)*(1/3) := by ring
      _    ≤ (-6)*(1/3) := by rel [h1]
      _    = -2 := by numbers
  · calc -2 = (-4)/2 := by numbers
          _ ≤ (2*s)/2 := by rel [h2]
          _ = s := by ring
  done
