/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open Function

/-!
# Bonus : racines d'un polynôme du second degré

`lemma mul_div_mul_left {c : ℝ} (a b : ℝ) (hc : c ≠ 0) : (c * a) / (c * b) = a / b`
-/

/-- Le but de cet exercice est de décrire les solutions de l'équation
`ax^2 + bx + c = 0` (avec `a ≠ 0`) lorsqu'il y en a, c'est à dire lorsque
`Δ = b^2 - 4ac ≥ 0`. Plus précisément, en supposant que `δ` est une racine de `Δ`,
on montre que les solutions sont `(-b ± δ) / 2a`. -/
example {a b c : ℝ} (ha : a ≠ 0) {δ : ℝ} (hδ : δ^2 = b^2 - 4*a*c) {x : ℝ} :
    a * x^2 + b*x + c = 0 ↔ x = (-b + δ)/(2*a) ∨ x = (-b - δ)/(2*a) := by
  have : a * (x - (-b + δ)/(2*a)) * (x - (-b - δ)/(2*a)) = a * x^2 + b*x + c := by
    sorry
    done
  sorry
  done
