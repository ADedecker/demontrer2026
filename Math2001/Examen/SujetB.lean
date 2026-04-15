import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.Parity

math2001_init

open Function

namespace Int

/-!
# Sujet B

**RAPPEL** : Vous devez
1. Renommer le fichier en `SujetB_Nom_Prenom.lean`
2. Mettre votre fichier sur Moodle à la fin de l'examen
-/

-- 2 points
example (x : ℝ) (h : x = 2 ∨ 2*x = -4) : x ^ 2 ≥ 3 := by
  sorry
  done

-- 2 points
example (x : ℝ) (h : 4*x + 8 = 6) : x < 1 ∨ x ≥ 2 := by
  sorry
  done

-- 3 points
example (n : ℤ) (hn : Odd n) : Even (n + 3) := by
  sorry
  done

-- 4 points
example (x : ℝ) : x ^ 2 - 7 * x + 12 = 0 ↔ (x = 3) ∨ (x = 4) := by
  sorry
  done

-- 4 points
example (f : ℝ → ℝ) (h : Injective f) : Injective (fun (x : ℝ) ↦ (f x) / 2) := by
  sorry
  done

-- 4 points
example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 - 1) := by
  sorry
  done

-- 2 points
example (x : ℝ) (h : x ≤ 2 ∧ x = 6) : x ^ 10 = -5 := by
  sorry
  done
