/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Library.Basic

math2001_init

open Real

/-!
# Quelques lemmes plus avancés

L'objectif de cette feuille bonus est de vous faire utiliser des lemmes plus
avancés de la bibliothèque à propos de fonctions continues.
Si `f : ℝ → ℝ` est une fonction, l'énoncé "f est continue" s'écrit `Continuous f`;
on vous demande de faire confiance que cette définition signifie ce dont vous avez l'habitude.

Pour écrire une fonction concrète, par exemple la fonction qui à `x` associe `x ^ 2 + 3`,
on écrit `fun (x : ℝ) => x ^ 2 + 3`.
-/

-- lemma continuous_id : Continuous (fun (x : ℝ) => x)
-- lemma continuous_const {c : ℝ} : Continuous (fun (x : ℝ) => c)

example : Continuous (fun (x : ℝ) => (0 : ℝ)) := by
  sorry
  done

-- lemma Continuous.add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
--   Continuous (fun (x : ℝ) => f x + g x)

example : Continuous (fun (x : ℝ) => x + 3) := by
  sorry
  done

example : Continuous (fun (x : ℝ) => x - pi) := by
  sorry
  done

-- `rexp` désigne la fonction exponentielle de `ℝ` dans `ℝ`.

-- lemma continuous_exp : Continuous (fun (x : ℝ) => rexp x)

example : Continuous (fun (x : ℝ) => x + rexp x) := by
  sorry
  done

-- lemma Continuous.mul {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
--   Continuous (fun (x : ℝ) => f x * g x)

example : Continuous (fun (x : ℝ) => x ^ 2 * rexp x) := by
  sorry
  done

-- lemma Continuous.comp {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
--   Continuous (fun (x : ℝ) => f (g x))

example : Continuous (fun (x : ℝ) => 3 * rexp (1 + x^2)) := by
  sorry
  done

example : Continuous (fun (x : ℝ) => rexp (rexp x)) := by
  sorry
  done
