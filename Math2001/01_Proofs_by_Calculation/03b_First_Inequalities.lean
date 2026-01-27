/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Bonus: Début des inégalités

Le contenu de ce fichier sera répété dans la feuille 4,
mais voici un aperçu pour les étudiant·e·s en avance.

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
-/


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

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
  sorry
  done
