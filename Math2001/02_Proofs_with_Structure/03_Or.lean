/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


-- le_or_succ_le {n a : ℤ} : n ≤ a ∨ a+1 ≤ n

-- eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℝ}  (h : a * b = 0) : a = 0 ∨ b = 0

-- ne_of_lt {a b : ℝ} (h : a < b) : a ≠ b

-- ou à l'hypothese (le plus compliqué c'est ca)
-- nommer les hypothéses generées
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


-- preuve par cas sur un entier (ou à l'hypothese en utilisant un lemme)
example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · sorry
  done


-- ou à la conclusion
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers
  done

-- à reecrire de facon plus lisible
-- apply un lemme à une hypothese
-- on peut le faire de la conclusion à la fin, c'est plus simple
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  sorry
  done

-- à faire tous seuls à la fin ?
-- mettre à la fin ?
-- faire au tableau et la montrer en lean ?
-- à faire la prochaine fois comme révision ?
example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        2 < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        2 < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]
  done


/-! # Exercises -/

-- les 3 premieres preuves sont exactement pareilles (type 1)
-- il faut les melanger avec les autres
-- pour empecher qu'ils copient le code d'avant

-- type 1
-- on a la tendance de vouloir commencer par la conclusion ici
-- on ne peut pas réecrire la conclusion avec addarith directement
-- on peut faire une hypothese hh : x^2 - 16 = 0 et apres trouver x
-- c'est quelquechose qu'on ferait en papier pour comprendre
-- mais ca ne sert pas à faire passer la preuve formelle en lean
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h1 | h2 := h
  · rw [h1]
    numbers
  · rw [h2]
    numbers
  done

-- type 1
-- l'enjeu n'est pas le meme quand on fait une preuve formelle
-- la partie semantique est moins important que la partie syntaxique
-- ca veut dire que la strategie a employée est plutot de
-- commencer par quelquepart et proceder de facon que la preuve
-- soit acceptée par la machine logiquement / syntaxiquement
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  have hh : x ^ 2 - 3 * x + 2 = (x-1)*(x-2) := by ring
  rw [hh]
  obtain h1 | h2 := h
  · rw [h1]
    numbers
  · rw [h2]
    numbers
  done

-- type 1
example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h2 := h
  · rw [h1]
    numbers
  · rw [h2]
    numbers
  done


-- type 1 mais avec ring car on a des variables
-- je ne lis meme pas l'énoncé
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h1 | h2 := h
  · rw [h1]
    ring
  · rw [h2]
    ring
  done

-------------------------------------------------------

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  sorry
  done

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  sorry
  done

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  sorry
  done

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry
  done

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  sorry
  done

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

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
  done
