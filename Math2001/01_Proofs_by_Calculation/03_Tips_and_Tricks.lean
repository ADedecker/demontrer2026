/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.3: Tips and tricks

Exercice : Traduire en Lean les preuves dans le texte -/

-- revision calc easy
-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  calc a = 2 * b + 5 := by rw [h1]
    _    = 2*3 +5 := by rw [h2]
    _    = 11 := by ring
  done


-- introduire addarith ici
-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  calc x = (x+4)-4 := by ring
    _    =  2 -4 := by rw [h1]
    _    = -2 := by ring
  done

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  addarith [h1]
  done


-- introduire have ici
-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have HB : b = 1 := by
    addarith [h2]
    done
  calc a = 4 + 5*b := by addarith [h1]
      _  = 4 + 5*1 := by rw [HB]
      _  = 9 := by ring
  done


-- EST-CE QUE CA VAUT LA PEINE DE FAIRE LES CALCS SUIVANTS ?
--
-- addarith ne marche pas
-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  calc w = ((3*w + 1) - 1)/3 := by ring
    _    = (4-1)/3 := by rw [h1]
    _    = 1 := by numbers
  done

-- addarith ne marche pas
-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 := by
  calc x = ((2*x + 3) - x) - 3 := by ring
    _    = (x - x) - 3 := by rw [h1]
    _    = -3 := by ring
  done

  ------------------------------------------------
  -- have + addarith + rw [] at
-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 := by
  have H : y = 2*x - 4 := by addarith [h1]
  rw [H] at h2
  calc x = (2 * x - 4 - x + 1) + 3 := by ring
    _    = 2 + 3 := by rw [h2]
    _    = 5 := by numbers
  done

-- interessant pour montrer qu'on peut structurer la preuve
-- comme en papier et utiliser le contexte en lean
-- Example 1.3.7
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 := by
  have H : 2*u = 10 := by
    calc 2*u = (u + 2 * v) + (u - 2 * v) := by ring
        _    =  4 + 6 := by rw [h1, h2]
        _    =  10 := by numbers
    done
  calc u = (2*u) / 2 := by ring
      _  = 10 /2 := by rw [H]
      _   = 5 := by ring
  done


--
-- Example 1.3.8
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 := by
  have H : y = 4 - x := by addarith [h1]
  rw [H] at h2
  have H2 : 8*x = 16 := by
    calc 8 * x = (5 * x - 3 * (4 - x)) + 12 := by ring
      _        = 4 + 12 := by rw [h2]
      _        = 16 := by ring
    done
  calc x = (8*x)/8 := by ring
      _  = 16 / 8 := by rw [H2]
      _  = 2 := by ring
  done
  done

/-! # Exercises

Résolvez ces problèmes vous-même.  Il peut être utile de les résoudre sur papier avant de
les saisir dans Lean. -/


example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  sorry
  done


example {a b : ℤ} (h : a - b = 0) : a = b := by
  sorry
  done


example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 := by
  sorry
  done


example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 := by
  sorry
  done


example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  sorry
  done


example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3) (h3 : c = 1) :
    a = 2 := by
  sorry
  done


example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 := by
  sorry
  done


example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by
  sorry
  done

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 := by
  sorry
  done

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 := by
  sorry
  done

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  sorry
  done


example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 := by
  sorry
  done


example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 := by
  sorry
  done


example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by
  sorry
  done

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by
  sorry
  done

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 := by
  sorry
  done
