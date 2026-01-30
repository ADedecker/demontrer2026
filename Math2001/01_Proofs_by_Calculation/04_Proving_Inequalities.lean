/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Inégalités

* `calc` gère aussi les suites d'égalités et d'inégalités (strictes et larges).
* `ring` et `rw` ne marchent que pour des égalités
* l'analogue de `rw` pour les inégalités est `rel`. Par exemple,
  si on sait que `h : a < b` et qu'on veut montrer `2 * a + 1 ≤ 2 * b + 1`,
  on peut `rel [h]` pour "remplacer `a` par `b`". Évidemment ce n'est pas toujours possible,
  par exemple on ne peut pas s'en servir pour montrer l'inégalité dans l'autre sens.
* `addarith` fonctionne avec les inégalités
* pour prouver des (in)égalités numériques, par exemple `2 - 3 < 0`, on ne peut
  pas utiliser `ring` comme on faisait pour les égalités. À la place,
  il y a la tactique `numbers` (qui gère aussi les égalités).
* `extra` montre des énoncés de la forme `machin + bidule ≥ machin` quand `bidule`
  est clairement positif (par exemple un carré).
-/

-- nouvelles tactiques : numbers et rel

-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x > 3) : y > 3 := by
  have : y > 3 - 2 * x := by addarith [hy]
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers
  done

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 := by
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]
  done

-- Example 1.4.2
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  calc
    r = (s + r + r - s) / 2 := by sorry
    _ ≤ (3 + (s + 3) - s) / 2 := by sorry
    _ = 3 := by sorry
  done

-- Example 1.4.3
-- Exercice : écrire l'ensemble de la preuve dans comme une preuve en Lean.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 := by
  sorry
  done

example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  sorry
  done

example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by
  sorry
  done

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  sorry
  done

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  sorry
  done

-- Example 1.4.4
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B := by
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by sorry
    _ ≤ A * B + A * B + A * v := by sorry
    _ ≤ A * B + A * B + 1 * v := by sorry
    _ ≤ A * B + A * B + B * v := by sorry
    _ < A * B + A * B + B * A := by sorry
    _ = 3 * A * B := by sorry
  done

-- Example 1.4.5
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by
  sorry
  done

-- Example 1.4.6
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 := by
  sorry
  done

-- Example 1.4.8
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 := by
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by sorry
    _ = 2 * (x ^ 2 + y ^ 2) := by sorry
    _ ≤ 2 * 1 := by sorry
    _ < 3 := by sorry
  done

-- Example 1.4.9
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
  3 * a * b + a ≤ 7 * b + 72 := by
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by sorry
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by sorry
    _ ≤ 2 * (8 * b) + 8 * a + a := by sorry
    _ = 7 * b + 9 * (a + b) := by sorry
    _ ≤ 7 * b + 9 * 8 := by sorry
    _ = 7 * b + 72 := by sorry
  done

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
  sorry
  done

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  sorry
  done

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  sorry
  done

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 := by
  sorry
  done

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 := by
  sorry
  done

-- Plus compliqué !
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  sorry
  done
