/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open Function

/-!
# Fiche de révisions
-/

example {x : ℝ} : x ^ 2 = 25 ↔ x = -5 ∨ x = 5 := by
  sorry
  done

example {x : ℝ} : x ^ 2 + 2 * x = 15 ↔ x = 3 ∨ x = -5 := by
  sorry
  done

example (f : ℝ → ℝ) (h : Surjective f) : ∀ c : ℝ, Surjective (fun x ↦ f (x + c)) := by
  sorry
  done

example (f : ℝ → ℝ) (h : Injective f) : ∀ c d : ℝ, Injective (fun x ↦ f (x - d) + c) := by
  sorry
  done

example (f : ℝ → ℝ) (g : ℝ → ℝ) (hf : Injective f) (hg : Injective g) :
    Injective (fun x ↦ f (g x)) := by
  sorry
  done
