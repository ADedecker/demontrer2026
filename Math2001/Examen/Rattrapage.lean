import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.Parity

math2001_init

open Function

namespace Int

/-!
# Sujet de Rattrapage

**RAPPEL** : Vous devez
1. Renommer le fichier en `Rattrapage_Nom_Prenom.lean`
2. Mettre votre fichier sur Moodle à la fin de l'examen
-/

-- 2 points
example (x : ℝ) (h : x + 4 = 1 ∨ 4 - x ≥ 2) : x ≤ 2 := by
  sorry
  done

-- 2 points
example (x : ℝ) (h : 4 - 3*x ≤ 0) : x ≥ 1 ∨ x < 0 := by
  sorry
  done

-- 4 points
example (m n : ℤ) (hm : Odd m) (hn : Odd n) : Even (m + n) := by
  sorry
  done

-- 4 points
example (x : ℝ) : x ^ 2 = 9 ↔ (x = -3) ∨ (x = 3) := by
  sorry
  done

-- 4 points
example (f : ℝ → ℝ) (h : Injective f) : Injective (fun (x : ℝ) ↦ (f x) + 3^4) := by
  sorry
  done

-- 4 points
example : ¬ Bijective (fun (x : ℝ) ↦ x^2 - x) := by
  sorry
  done
