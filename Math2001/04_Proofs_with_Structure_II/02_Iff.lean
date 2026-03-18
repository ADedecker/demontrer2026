/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers
  done

example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    calc x = ((2*x - 1) + 1)/2 := by ring
      _    = (11 + 1)/2 := by rw [h]
      _    = 6 := by numbers
  · intro h
    rw [h]
    numbers
  done

example {x : ℝ} : 5 * x + 22 = 12 ↔ x = -2 := by
  constructor
  · intro h
    calc x = ((5*x + 22) - 22)/5 := by ring
      _    = (12-22)/5 := by rw [h]
      _    = -2 := by numbers
  · intro h
    rw [h]
    numbers
  done

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have racines : (x+3)*(x-2) = 0 := by
      calc (x+3)*(x-2) = x^2 + x -6 := by ring
        _ = 0 := by rw [h]
    have hh : (x+3)= 0 ∨ (x-2) = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero
      rw [racines]
    obtain h1 | h2 := hh
    · left
      addarith [h1]
    · right
      addarith [h2]
  · intro h
    obtain  h1 | h2  := h
    · rw [h1]
      numbers
    · rw [h2]
      numbers
  done

-- mettre des equations second degré à la revision

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have hh : a ^ 2 - 5 * a + 6 ≤ 0 := by addarith [h]
    have hhh : a ^ 2 - 5 * a + 6 = (a-3)*(a-2) := by ring
    -- difficile
    sorry
  · intro h
    obtain h2 | h3 := h
    · rw [h2]
      numbers
    · rw [h3]
      numbers
  done

-- Plus difficile
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    have hh : k^2 < 3^2 := by
      calc k^2 ≤ 6 := by rel [h]
        _      < 9 := by numbers
    have h3 : k < 3 := by cancel 2 at hh
    -- c'est evident mathematiquement mais il faut plus des lemmes non ?
    sorry


  · intro h
    obtain h | h | h := h
    · rw [h]
      numbers
    · rw [h]
      numbers
    · rw [h]
      numbers
  done
