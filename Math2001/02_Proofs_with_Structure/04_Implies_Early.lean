/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- utiliser une hypothese
example {x : ℝ} (h : x < 0 → x = -1) (h2 : 2 * x + 1 ≤ 0) :
    x = -1 := by
  apply h
  have h3 : 2 * x ≤ - 1 := by addarith [h2]
  calc
    x = (2 * x) / 2 := by ring
    _ ≤ (- 1) / 2 := by rel [h3]
    _ < 0 := by numbers
  done

-- introduire une hypothese
example {x : ℝ} (h : x < 0 → x = -1) :
    2 * x + 1 ≤ 0 → x = -1 := by
  intro h2
  apply h
  have h3 : 2 * x ≤ - 1 := by addarith [h2]
  calc
    x = (2 * x) / 2 := by ring
    _ ≤ (- 1) / 2 := by rel [h3]
    _ < 0 := by numbers
  done

-- `lemma lt_trichotomy (x y : ℝ) : x < y ∨ x = y ∨ x > y`

-- c'est quoi l'idée ?
example {x : ℝ} (h : x < 0 → x = -1) : x ≥ -1 := by
  sorry
  done
