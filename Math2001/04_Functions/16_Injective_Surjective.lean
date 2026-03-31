/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
# Fonctions injectives, Fonctions surjectives

Rappels:
* `push_neg` (ou `push_neg at h`) simplifie des négations
* `dsimp [f]` (ou `dsimp [f] at h`) remplace les occurrences de `f` par sa définition

def Injective (f : X → Y) : Prop :=
  ∀ a₁ a₂ : X, f a₁ = f a₂ → a₁ = a₂

def Surjective (f : X → Y) : Prop :=
  ∀ b : Y, ∃ a : X, f a = b

-/

open Function
namespace Int

def q (x : ℝ) : ℝ := x + 3

example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]
  done

example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · numbers
  · numbers
  done

def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring
  done

example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra
  done

/-!
## Exercices
-/

/-- Il y a des paires d'énoncés du type `example : 1 + 1 = 2` et `example : ¬(1 + 1 = 2)`.
Bien évidemment un est vrai et l'autre est faux. À vous de trouver lequel est faisable. -/

example : Injective (fun (x : ℚ) ↦ x - 12) := by
  sorry
  done
example : ¬ Injective (fun (x : ℚ) ↦ x - 12) := by
  sorry
  done

example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry
  done
example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  sorry
  done

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry
  done
example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry
  done

example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry
  done
example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry
  done

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry
  done
example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry
  done

example : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry
  done
example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry
  done

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry
  done
example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry
  done

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry
  done
example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry
  done

example : ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  sorry
  done
example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  sorry
  done

example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry
  done
example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry
  done

example : Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  sorry
  done
example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  sorry
  done

-- Tous les énoncés à partir d'ici sont vrais. Vous pouvez les prouver.

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  sorry
  done

example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by
  sorry
  done

-- Plus difficile, allez d'abord faire la feuille suivante

-- Indication : `x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2)`
example : Injective (fun (x:ℝ) ↦ x ^ 3) := by
  sorry
  done
