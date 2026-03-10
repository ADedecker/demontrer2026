/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- le_or_gt (x y : ℝ) : x ≤ y ∨ x > y

-- il faut mettre les lemmes en tete de la fiche

-- utiliser une hypothese avec il exists - tactique obtain encore
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra
  done


-- exercice ?
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · sorry
  done


-- introduire il exists - tactique use
example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers
  done


-- introduire il exists - temoin dependant du contexte
example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra
  done


-- exercice use
-- il faut les trouver sur papier
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers
  done


-- exercice use
-- il faut trouver les m et n dependant de a
-- facile si tu as l'idée
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1
  use a
  ring
  done


-- exercice use
-- il faut trouver un x entre p et q
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  · sorry
  · sorry
  done


-- exemple tactique use
-- pas tres interessant à mon avis
example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  · numbers
  · constructor
    · numbers
    · constructor
      numbers
      numbers
  done

/-! # Exercises -/

-- les premiers exercices sont pour apprendre la tactique

-- tres facile - use
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers
  done

-- tres facile - use
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6
  use 7
  numbers
  done

-- tres facile - use
example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  · numbers
  · numbers
  done

-- facile - use
-- toute la difficulté est de trouvers les entiers
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4
  use 3
  numbers
  done

-- plus compliquée
-- peut etre on peutle faire plus facilement
-- sans trichotomy ?
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have h : x < 0 ∨ x=0 ∨ x > 0 := by apply lt_trichotomy
  obtain h1 | h2 | h3 := h
  · use 1
    calc x < 0 := by rel [h1]
      _ < 1^2 := by numbers
  · use 1
    rw [h2]
    numbers
  · use x+1
    have h : x ^ 2 > 0 := by extra
    have hh : (x+1)^2 - x > 0 := by
      calc (x+1)^2 - x = x^2 + x +1 := by ring
        _              > 0 + 0 + 1 := by rel [h3, h]
        _              > 0 := by numbers
    addarith [hh]
  done


-- obtain
-- la plus difficile au niveau des strategies
-- disjonction des cas
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨ x, hx ⟩ := h
  sorry
  done



-- le_or_gt (x y : ℝ) : x ≤ y ∨ x > y
-- PLUS COMPLIQUÉ
-- obtain AVEC UN TROU TODO
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨ x, hx ⟩ := h
  have h : x ≤ 2 ∨ x > 2 := by apply le_or_gt
  obtain h | h := h
  · rw [← hx]
    apply ne_of_lt
    calc 2*x ≤ 2*2 := by rel [h]
      _      < 5 := by numbers

  · rw [← hx]
    apply ne_of_gt
    have hx2 : x ≥ 3 := by sorry
    calc 2*x ≥ 2*3 := by rel [hx2]
      _      > 5 := by numbers
  done



-- use difficile
-- calc tres penibles
-- je doute sur l'utilité de l'exrcice
example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  have h : n ≤ 0 ∨ n > 0 := by apply le_or_gt
  obtain h | h := h
  · use 2
    sorry
  · use n+1
    sorry
  done


-- use
-- facile si tu as l'idée de faire a ≤ b+c => b+c-a ≥ 0
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
  done
