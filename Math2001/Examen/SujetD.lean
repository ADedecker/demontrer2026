import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.Parity

math2001_init

open Function

namespace Int

/-!
# Sujet D

**RAPPEL** : Vous devez
1. Renommer le fichier en `SujetD_Nom_Prenom.lean`
2. Mettre votre fichier sur Moodle à la fin de l'examen
-/

-- 2 points
example (x : ℝ) (h : x + 1 = 0 ∨ 2*x - 2 = 0) : x ≤ 1 := by
  sorry
  done

-- 2 points
example (x : ℝ) (h : 2*x + 2 = -8) : x = -5 ∨ x = 25 := by
  sorry
  done

-- 3 points
example (n : ℤ) (hn : Even n) : Odd (3 * n - 1) := by
  sorry
  done

-- 4 points
example (x : ℝ) : x ^ 2 - 5 * x = 0 ↔ (x = 5) ∨ (x = 0) := by
  sorry
  done

-- 4 points
example (f : ℝ → ℝ) (h : Surjective f) : Surjective (fun (x : ℝ) ↦ f (3 * x)) := by
  sorry
  done

-- 4 points
example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 6) := by
  sorry
  done

-- 2 points
example (x : ℝ) (h : x ≤ 1 ∧ x = 60) : x < x := by
  sorry
  done
