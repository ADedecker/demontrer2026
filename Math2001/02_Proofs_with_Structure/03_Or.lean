/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


-- le_or_succ_le {n a : ℤ} : n ≤ a ∨ a+1 ≤ n

-- eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℝ}  (h : a * b = 0) : a = 0 ∨ b = 0

-- ne_of_lt {a b : ℝ} (h : a < b) : a ≠ b
-- ne_of_gt {a b : ℝ} (h : a > b) : a ≠ b


------------------------------------------------------------
-- TYPE 1 OU À L'HYPOTHESE
-- tactique obtain
-- (nommer les hypothéses generées)

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


------------------------------------------------------------
-- TYPE 4 OU À L'HYPOTHESE (en utilisant un lemme)
-- preuve par cas sur un entier
-- le_or_succ_le {n a : ℤ} : n ≤ a ∨ a+1 ≤ n

-- strategie :
-- (1) on doit trouver le bon a
-- (2) on utilise le lemme le_or_succ pour créer la bonne hypothese avec OU
-- (3) on fait la distinction des cas
-- (4) dans chaque sous-preuve on doit appliquer le bon lemme


example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · sorry
  done


------------------------------------------------------------
-- TYPE 2 OU À LA CONCLUSION
-- tactiques right left
-- (choisir quel coté, on va demontrer)

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers
  done



------------------------------------------------------------
-- TYPE 3 OU À LA CONCLUSION ET À L'HYPOTHESE
-- équation deuxieme degré
-- apply un lemme à une hypothese

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 : (x - 1) * (x - 2) = 0 := by
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  sorry
  done



------------------------------------------------------------
-- TYPE 4 COMPLET
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

-- TYPE 1 :
-- on a la tendance de vouloir commencer par la conclusion ici
-- on ne peut pas réecrire la conclusion avec addarith directement
-- on peut faire une hypothese hh : x^2 - 16 = 0 et apres trouver x
-- c'est quelquechose qu'on ferait en papier pour comprendre
-- mais ca ne sert pas à faire passer la preuve formelle en lean
--
-- l'enjeu n'est pas le meme quand on fait une preuve formelle
-- la partie semantique est moins important que la partie syntaxique
-- ca veut dire que la strategie à employer est plutot de
-- commencer par quelquepart et proceder de facon que la preuve
-- soit acceptée par la machine logiquement / syntaxiquement


-- TYPE 1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h1 | h2 := h
  · rw [h1]
    numbers
  · rw [h2]
    numbers
  done

-- TYPE 1
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
-- type 2 : OU dans la conclusion
-- pratique right left

-- type 2 simple
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  addarith [h]
  done

-- type 2 simple (calc un peu compliqué mais ok)
example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  calc b = (a + 2*b)/2 - a/2 := by ring
      _  < 0/2 - a/2 := by rel [h]
      _ = -a/2 := by ring
  done


-- type 2 simple
-- probleme avec extra ici
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  have hx : x = y/2 - 1/2 := by
    calc x = (2*x + 1)/2 - 1/2 := by ring
        _  = y/2 - 1/2 := by rw [h]
  left
  rw [hx]
  calc y/2 - 1/2 =  y/2 + (-(1/2)) := by ring
            _    <  y/2 + 0 := by sorry
            _    =  y/2 := by ring
  done


-------------------------------------------------------
-- type 3 équation deuxieme degré
-- application de lemme à une hypothese
-- (1) il faut créer une hypothese de la bonne forme pour appliquer le lemme
-- (2) on applique le lemme
-- (3) on distingue des cas

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 : x ^ 2 + 2 * x - 3 = (x + 3)*(x-1) := by ring
  have h2 : (x + 3)*(x - 1) = 0 := by
    rw [← h1]
    rw [hx]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h2
  obtain h3 | h4 := h2
  · left
    addarith [h3]
  · right
    addarith [h4]
  done

-- type 3 par rapport à la strategie
-- mais avec 2 variables
-- (a - b)*(a - 2b) = a^2 - 2ab - ab + 2b^2
example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) :
  a = b ∨ a = 2 * b := by
  have h1 : (a - b)*(a - 2*b) = 0 := by
    calc (a - b)*(a - 2*b) = a^2 - 3*a*b + 2*b^2 := by ring
      _                    = 0 := by addarith [hab]
    done
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  obtain h2 | h3 := h1
  · left
    addarith [h2]
  · right
    addarith [h3]
  done


-- type 3 par rapport à la strategie
--  on utilise cancel pour le carré
example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 : t^2 * (t-1) = 0 := by
    calc t^2 * (t-1) = t ^ 3 - t ^ 2 := by ring
      _              = 0 := by addarith [ht]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  obtain h2 | h3 := h1
  · right
    cancel 2 at h2
  · left
    addarith [h3]
  done

-------------------------------------------------------------------

-- type 4: preuve par cas n < m OU n ≥ m+1 pour un m fixé

-- le_or_succ_le {n a : ℤ} : n ≤ a ∨ a+1 ≤ n
-- ne_of_lt {a b : ℝ} (h : a < b) : a ≠ b
-- ne_of_gt {a b : ℝ} (h : a > b) : a ≠ b

-- strategie :
-- (1) on doit trouver le bon a
-- (2) on utilise le lemme le_or_succ pour créer la bonne hypothese avec OU
-- (3) on fait la distinction des cas
-- (4) dans chaque sous-preuve on doit appliquer le bon lemme

-- type 4
example {n : ℕ} : n ^ 2 ≠ 7 := by
  have hn := le_or_succ_le n 2
  obtain h1 | h2 := hn
  · apply ne_of_lt
    calc n^2 ≤ 2^2 := by rel [h1]
      _      < 7 := by numbers
    done
  · apply ne_of_gt
    calc n^2 ≥ 3^2 := by rel [h2]
      _ > 7 := by numbers
  done


-- type 4
example {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 1
  obtain h1 | h2 := hx
  · apply ne_of_lt
    calc 2*x ≤ 2*1 := by rel [h1]
      _      = 2 := by numbers
      _      < 3 := by numbers
    done
  · apply ne_of_gt
    calc 2*x ≥ 2*2 := by rel [h2]
      _      > 3 := by numbers
    done
  done

-- type 4
example {t : ℤ} : 5 * t ≠ 18 := by
  have ht := le_or_succ_le t 3
  obtain h1 | h2 := ht
  · apply ne_of_lt
    calc 5*t ≤ 5*3 := by rel [h1]
      _      < 18 := by numbers
    done
  · apply ne_of_gt
    calc 5*t ≥ 5*4 := by rel [h2]
        _    > 18 := by numbers
    done
  done

-- type 4
-- have to find the right number for the lemma le_or_succ_le
example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
  done
