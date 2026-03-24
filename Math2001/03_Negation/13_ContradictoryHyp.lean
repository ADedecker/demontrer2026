/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
# Hypothèses Contradictoires
-/

example (x y : ℝ) (hx1 : x = 1) (hx2 : x = 2) : y = 4 := by
  have hx3 : x ≠ 1 := by
    rw [hx2]
    numbers
    done
  contradiction
  done

example (x y : ℝ) (hx1 : x = 1) (hx2 : x = 2) : y = 4 := by
  rw [hx1] at hx2
  numbers at hx2
  done

example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have H : ¬0 < x * y := by
      apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
      done
    contradiction
  · -- the case `0 < y`
    apply hpos
  done

/-
## Exercices
-/

example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  sorry
  done

example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) : y ≤ x := by
  sorry
  done

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  sorry
  done

-- **Exercice plus difficile : allez d'abord faire les fichiers 14 et 15 !**
-- Vous pourrez utiliser la tactique `interval_cases`, qui dit (par exemple)
-- que si `n : ℕ` vérifie `0 < n` et `n ≤ 2`, alors `n = 1` ou `n = 2`.

example {n : ℕ} (h : 0 < n) (hb : n ≤ 2) : n = 1 ∨ n = 2 := by
  interval_cases n
  · left
    numbers
    done
  · right
    numbers
    done
  done

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  sorry
  done
