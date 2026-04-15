import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.Parity

math2001_init

open Function

namespace Int

/-!
# Sujet A

**RAPPEL** : Vous devez
1. Renommer le fichier en `SujetA_Nom_Prenom.lean`
2. Mettre votre fichier sur Moodle à la fin de l'examen
-/

-- 2 points
example (x : ℝ) (h : x + 1 = 0 ∨ 3*x - 3 < 0) : x < 1 := by
  sorry
  done

-- 2 points
example (x : ℝ) (h : 4*x - 2 = 6) : x < 1 ∨ x ≥ 2 := by
  sorry
  done

-- 3 points
example (n : ℤ) (hn : Even n) : Odd (n + 3) := by
  sorry
  done

-- 4 points
example (x : ℝ) : x ^ 2 - x - 2 = 0 ↔ (x = -1) ∨ (x = 2) := by
  sorry
  done

-- 4 points
example (f : ℝ → ℝ) (h : Injective f) : Injective (fun (x : ℝ) ↦ f (x - 1)) := by
  sorry
  done

-- 4 points
example : ¬ Bijective (fun (x : ℝ) ↦ (x - 1) ^ 2) := by
  sorry
  done

-- 2 points
example (x : ℝ) (h : x ≤ 2 ∧ x = 6) : 2 * x = 2428372 := by
  sorry
  done
