/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.4: Proving inequalities -/

-- nouvelles tactiques : numbers et rel

-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers
  done

-- Example 1.4.2
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
-- JE L'AI FAIT SANS REFLECHIR / COMPRENDRE LA PREUVE
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h2, h1]
    _ = 3 := by ring
  done

-- PREUVE AVEC DES ETAPES INTERMEDIAIRES
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r - s ≤ 3 := by addarith [h1]
  have h4 : 2*r ≤ 6 := by
    calc 2 * r = (s + r) + (r - s) := by ring
      _        ≤ 3 + (r - s) := by rel [h2]
      _        ≤ 3 + 3 := by rel [h3]
      _        = 6 := by ring
    done
  calc r = (2*r)/2 := by ring
      _  ≤ 6 / 2 := by rel [h4]
      _ = 3 := by numbers
  done
  done

-- Example 1.4.3
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 := by
  calc x + y ≤ (x+5) - 2 := by addarith[h1, h2]
      _      = x + 3 := by ring
      _      ≤ -2 + 3 := by rel [h2]
      _      = 1 := by ring
      _      < 2 := by numbers
  done



-- Example 1.4.4
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
-- pas sure que cet exercice est interessant car c'est difficile de lire
-- le contexte quand on est dans le calc block
-- pedagogiquement c'est interessant car c'est une preuve avec des trous
-- mais elle est tres syntaxique, on ne doit pas forcement comprendre l'enoncé
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B := by
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel[h4, h5]
    _ ≤ A * B + A * B + A * v := by rel [h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel [h2]
    _ ≤ A * B + A * B + B * v := by rel [h3]
    _ < A * B + A * B + B * A := by rel [h9]
    _ = 3 * A * B := by ring
  done


-- Example 1.4.5
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
-- astuce t*t ≥ 10t
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by
  have h : t^2 ≥ 10*t := by
    calc t^2 = t*t := by ring
      _      ≥ 10*t := by rel[ht]
  calc t^ 2 - 3 * t -17 ≥ 10*t - 3*t -17 := by rel [h]
                  _     = 7*t - 17 := by ring
                  _     ≥ 7*10 - 17 := by rel [ht]
                  _     ≥ 5 := by numbers
  done

-- Example 1.4.6
-- same as above
/- n^2 -2n -11 > 0
  n^2 - 2n - 11 > 5n - 2n -11 = 3n - 11 > 3*5 - 11 = 4 > 0
 -/
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 := by
  have H0 : n^2 ≥ 5*n := by
    calc n^2 = n*n := by ring
      _      ≥ 5*n := by rel[hn]
  have H1 : n^2 - 2*n - 11 > 0 := by
    calc n^2 - 2*n - 11 ≥ 5*n - 2*n - 11 := by rel [H0]
                      _ = 3*n - 11 := by ring
                      _ ≥ 3*5 - 11 := by rel [hn]
                      _ = 4 := by numbers
                      _ > 0 := by numbers
  addarith [H1]
  done



-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 := by
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]
  done


-- Example 1.4.8
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
-- preuve par trous
-- interessant mais on n'est pas obligés de comprendre l'enoncé pour le demontrer
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 := by
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel [h]
    _ < 3 := by numbers
  done


-- Example 1.4.9
-- Exercice : remplacez les mots `sorry` par une tactique en Lean.
-- preuve à trous  - interessant car ca fait reflechir
-- lire le syntaxe sans ecrire est un autre registre
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
  3 * a * b + a ≤ 7 * b + 72 := by
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by extra
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel [h3]
    _ = 7 * b + 72 := by ring
  done


-- Example 1.4.10
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by extra
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring
  done


/-! # Exercises

Résolvez ces problèmes vous-même.  Il peut être utile de les résoudre sur papier avant de
les saisir dans Lean. -/


-- entrainement rel SIMPLE
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by
  calc x = (x+3)-3 := by ring
    _    ≥ 2*y -3 := by rel [h1]
    _    ≥ 2*1 -3 := by rel [h2]
    _    = -1 := by numbers
  done

-- on doit reflechir
-- avec HAVE on peut ecrire forward ce qui est plus intuitif
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
  have h4 : (a+2*b)-3 ≥ 4-a := by rel [h2,h1]
  have h5 : (a+2*b)+a ≥ 4+3 := by addarith [h4]
  calc a+b = (2*a + 2*b)/ 2 := by ring
    _      = ((a+2*b)+a) / 2 := by ring
    _      ≥ (4+3) /2 := by rel [h5]
    _      ≥ 3 := by numbers
  done


----------- meme technique


example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  have H0 : x^3 ≥ 9*x^2 := by
    calc x^3 = x*x^2 := by ring
        _    ≥ 9*x^2 := by rel [hx]
  calc x^3 - 8*x^2 +2*x ≥ 9*x^2 - 8*x^2 + 2*x := by rel [H0]
                      _ = x^2 + 2*x := by ring
                      _ = x*x + 2*x := by ring
                      _ ≥ 9*9 + 2*9 := by rel [hx]
                      _ ≥ 3 := by numbers
  done



-- un peu chiant n^4
-- extra fait un peu trop ici (elle trouve que n!=0)
example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 := by
  have h0 : n^2 > 0 := by extra
  have H0 : (n^2 - 3*n - 2) > 0 := by
    calc n^2 - 3*n - 2 = n*n - 3*n - 2 := by ring
                    _  ≥ 10*n- 3*n - 2 := by rel [hn]
                    _ = 7*n - 2 := by ring
                    _ ≥ 7*10 - 2 := by rel [hn]
                    _ > 0 := by numbers
  have H1 : n ^ 4 - 2 * n ^ 2 - 3 * n ^ 3 > 0 := by
    calc n ^ 4 - 2 * n ^ 2 - 3 * n ^ 3 = n^2 * (n^2 - 3*n - 2) := by ring
                                    _  > 0*0 := by rel [h0, H0] -- extra le fait aussi
                                    _ = 0 := by numbers
  addarith [H1]
  done

-- meme technique de decomposition
example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 := by
  calc n ^ 2 - 2 * n + 3 = n*n - 2*n + 3 := by ring
                      _  ≥ 5*n - 2*n + 3 := by rel [h1]
                      _  = 3*n + 3 := by ring
                      _  ≥ 3*5 + 3 := by rel [h1]
                      _ > 14 := by numbers
  done

----------------------------------------
-- extra simple (move up ?)
example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  have H : x ^ 2 - 2 * x + 1 ≥ 0 := by
    calc x ^ 2 - 2 * x + 1 = (x-1)^2 := by ring
                        _  ≥ 0 := by extra
  addarith [H]
  done

-- extra simple (move up)
example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  have H : a^2 + b^2 - 2*a*b ≥ 0 := by
    calc a^2 + b^2 - 2*a*b = (a-b)^2 := by ring
                      _    ≥ 0 := by extra
  addarith [H]
  done


example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : (b+a) ≥ 0 := by addarith [h1]
  have h4 : (b-a) ≥ 0 := by addarith [h2]
  have h5 : (b+a)*(b-a) ≥ 0 := by extra
  have h6 : b^2 - a^2 ≥ 0 := by
    calc b^2 - a^2 = (b+a)*(b-a) := by ring
              _    ≥ 0 := by rel [h5]
  addarith [h6]
  done


-- b^3 - a^3 = (b-a)*(b^2 + a*b + a^2)
-- (b + a/2)^2 = b^2 + (2*b*a)/2 + (a^2)/4
-- b^2 + a*b + a^2 = (b + a/2)^2 + (3*a^2)/4
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1 : b-a ≥ 0 := by addarith [h]
  have h2 : b^2 + a*b + a^2 = (b + a/2)^2 + (3* a^2)/4 := by ring
  have h3 : b^3 - a^3 ≥ 0 := by
    calc b^3 - a^3 = (b-a)*(b^2 + a*b + a^2) := by ring
          _        = (b-a)*((b + a/2)^2 + (3* a^2)/4) := by ring
          _        ≥ 0 := by extra
  addarith [h3]
  done
