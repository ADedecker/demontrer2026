/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
set_option pp.funBinderTypes true

noncomputable section

/-!
# Composition de fonctions

La tactique `ext` transforme `f = g` en `∀ x, f x = g x`.

`lemma comp_apply {f : X → Y} {g : Y → Z} {x : X} : (g ∘ f) x = g (f x)`
-/

open Function

def f (a : ℝ) : ℝ := a + 3
def g (b : ℝ) : ℝ := 2 * b
def h (c : ℝ) : ℝ := 2 * c + 6

example : g ∘ f = h := by
  ext x
  calc (g ∘ f) x = g (f x) := by rw [comp_apply]
    _ = 2 * (x + 3) := by dsimp [f, g]
    _ = 2 * x + 6 := by ring
    _ = h x := by dsimp [h]
  done

def s (x : ℝ) : ℝ := 5 - x

example : s ∘ s = id := by
  ext x
  dsimp [s]
  ring
  done

def Inverse {X Y : Type} (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

example : Inverse s s := by
  dsimp [Inverse]
  constructor
  · ext x
    dsimp [s]
    ring
  · ext x
    dsimp [s]
    ring
  done

theorem exists_inverse_of_bijective {X Y : Type} {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨h_inj, h_surj⟩ := hf
  dsimp [Surjective] at h_surj
  choose g hg using h_surj
  use g
  dsimp [Inverse]
  constructor
  · -- prove `g ∘ f = id`
    ext x
    dsimp [Injective] at h_inj
    apply h_inj
    calc f ((g ∘ f) x) = f (g (f x)) := by rw [comp_apply]
      _ = f x := by apply hg
      _ = f (id x) := by dsimp [id]
  · -- prove `f ∘ g = id`
    ext y
    apply hg
  done

theorem bijective_of_inverse {X Y : Type} {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by dsimp [id]
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rw [comp_apply]
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rw [comp_apply]
      _ = id x2 := by rw [hgf]
      _ = x2 := by dsimp [id]
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rw [comp_apply]
      _ = id y := by rw [hfg]
      _ = y := by dsimp [id]

theorem bijective_iff_exists_inverse {X Y : Type} (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g := by
  constructor
  · apply exists_inverse_of_bijective
  · intro h
    obtain ⟨g, H⟩ := h
    apply bijective_of_inverse H


/-! # Exercices -/

def u (x : ℝ) : ℝ := 5 * x + 1

-- Il faut trouver la bonne définition pour l'inverse de `u`
def v (y : ℝ) : ℝ := (y-1)/5

example : Inverse u v := by
  dsimp [Inverse]
  constructor
  · ext x
    calc (v ∘ u) x = v (u x) := by rw [comp_apply]
    _ = ((5*x +1) - 1)/5 := by dsimp [v, u]
    _ = x := by ring
  · ext x
    calc (u ∘ v) x = u (v x) := by rw [comp_apply]
      _ = 5 * ((x - 1)/ 5) + 1 := by dsimp [u, v]
      _ = x := by ring
  done

example {X Y : Type} {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective]
  intro x1 x2 hgf
  apply hg at hgf
  apply hf at hgf
  apply hgf
  done

example {X Y : Type} {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective]
  intro z
  have H1 : ∃ y, g y = z := by apply hg
  obtain ⟨y, H2⟩ := H1
  have H3 : ∃ x, f x = y := by apply hf
  obtain ⟨x, H4⟩ := H3
  use x
  rw [H4]
  apply H2
  done

example {X Y : Type} {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse] at h
  dsimp [Inverse]
  obtain ⟨H1, H2⟩ := h
  constructor
  · apply H2
  · apply H1
  done

-- Plus difficile

example {X Y : Type} {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  sorry
  done
