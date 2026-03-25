/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init

example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP : P
  · apply hP
  · contradiction
  done

/-! # Exercises -/

example (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      apply h
      apply hP
    · left
      apply hP
  · intro h
    intro hP
    obtain h | h := h
    · contradiction
    · apply h
  done

example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intro h hQ
    by_cases hP : P
    · apply hP
    · have hQ2 : ¬ Q := by apply (h hP)
      contradiction
  · intro h notP
    by_cases hP : P
    · contradiction
    · by_cases hQ : Q
      · have hP2 : P := by apply (h hQ)
        contradiction
      · apply hQ
  done
