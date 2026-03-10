/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Theory.Parity

math2001_init

open Int

/-!
# Parité

**Rappel**: vous pouvez trouver la liste des lemmes vus en cours dans le fichier `lemmes.lean`.
-/

-- def Odd (n : ℤ) : Prop := ∃ k, n = 2 * k + 1
-- def Even (n : ℤ) : Prop := ∃ k, n = 2 * k

example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at hn
  dsimp [Odd]
  -- Variante: `dsimp [Odd] at *`
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring

/-!
## Exercices
-/

example : Odd (-9 : ℤ) := by
  sorry
  done

example : Even (26 : ℤ) := by
  sorry
  done

example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  sorry
  done

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  sorry
  done

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  sorry
  done

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  sorry
  done

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  sorry
  done

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  sorry
  done

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  sorry
  done

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry
  done

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  sorry
  done

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  sorry
  done
