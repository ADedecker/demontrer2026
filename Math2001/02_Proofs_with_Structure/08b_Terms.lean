/- Copyright (c) Anatole Dedecker, 2026.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-!
# Termes de preuve

**Cette feuille est facultative : il est plus important de maîtriser le reste du cours !**

L'objectif de cette feuille est d'expliquer le lien entre programmation fonctionelle et
démonstrations mathématiques, qui est au coeur du fonctionnement de Lean
-/

/-!
## Partie 1 : Lean est un langage fonctionnel

En plus d'être un assistant de preuve, Lean est un langage de programmation fonctionelle
très puissant, comparable à OCaml et Haskell. Voici quelques exemples.
-/

/-- Exemple: la fonction `n ↦ 2 * n + 1`. -/
def f : ℕ → ℕ :=
  fun n => 2 * n + 1

/- `#eval` permet d'évaluer des expressions. Évidemment c'est aussi possible de compiler
un programme, mais ce n'est pas ce qui nous intéresse aujourd'hui. -/
#eval f 30

/-- Une autre manière de définir la fonction `f`. -/
def f_v2 (n : ℕ) : ℕ :=
  2 * n + 1

/-- Exemple: la fonction "factorielle". -/
def fac (n : ℕ) : ℕ :=
  match n with
    | 0 => 1
    | k+1 => (k+1) * fac k

-- Les entiers de Lean ont une précision arbitraire : il n'y a pas d'overflow
#eval fac 50

/- `List X` est le type des listes d'éléments de `X`. Vous pouvez faire `Ctrl + Click` pour aller
voir la définition -/
#check List

/-- Exemple: une implémentation de la fonction "rajouter à la fin". Cette fonction
existe déjà en tant que `List.concat` -/
def myConcat (l : List ℕ) (x : ℕ) : List ℕ :=
  match l with
  | [] => [x]
  | a :: l' => a :: (myConcat l' x)

#eval myConcat [1, 3, 4] 2

/- Une fonctionalité de Lean qui n'est pas présente dans OCaml est que, par défaut,
Lean vous empêche de faire des boucles infinies.
Par exemple, le code suivant ne compile pas. -/

/-
def myConcatError (l : List ℕ) (x : ℕ) : List ℕ :=
  match l with
  | [] => [x]
  | a :: l' => a :: (myConcatError l x)
-/

/- Voici d'autres exemples pour vous donner une idée de la syntaxe. -/

/-- La fonction "inverser la liste". -/
def reverse (l : List ℕ) : List ℕ :=
  let rec aux (input : List ℕ) (output : List ℕ) : List ℕ :=
    match input with
    | [] => output
    | a :: input' => aux input' (a :: output)
  aux l []

#eval reverse [1, 2, 3]

/-- **Exercice** : Coder la fonction "somme des termes d'une liste". -/
def sum (l : List ℕ) : ℕ :=
  sorry

/-- La fonction "tri par insertion". -/
def insertion_sort (l : List ℕ) : List ℕ :=
  let rec insert_sorted (x : ℕ) (sorted : List ℕ) : List ℕ :=
    match sorted with
    | [] => [x]
    | a :: sorted' => if a < x then a :: (insert_sorted x sorted') else x :: sorted
  match l with
  | [] => []
  | a :: l' => insert_sorted a (insertion_sort l')

#eval insertion_sort [4, 1, 3, 2, 5]

/-- On peut aussi définir notre propre "type algébrique" (on parle plutôt de "type inductif").
Par exemple, voici une définition d'un arbre binaire dont les sommets contiennent des entiers. -/

inductive BinaryTree : Type
| leaf : BinaryTree
| node (n : ℕ) (left : BinaryTree) (right : BinaryTree) : BinaryTree

/-- Le maximum d'un arbre binaire. Ici, `t.max` peut être utilisé pour dire `BinaryTree.max t`. -/
def BinaryTree.max (t : BinaryTree) : ℕ :=
  match t with
  | leaf => 0
  | node n l r => Nat.max n (Nat.max l.max r.max)

#eval BinaryTree.max
  (BinaryTree.node 3
    (BinaryTree.node 0 BinaryTree.leaf (BinaryTree.node 100 BinaryTree.leaf BinaryTree.leaf))
    (BinaryTree.node 25 BinaryTree.leaf BinaryTree.leaf))

/-!
## Partie 2 : Le lien avec la logique

À ce stade, le lien avec le fait d'écrire des démonstrations n'est pas clair. En fait il y a un
lien très profond, l'**isomorphisme de Curry-Howard**, qui est au coeur du fonctionnement de Lean.

En deux mots : une proposition/énoncé `P`, c'est un ***type***, dont les éléments sont les
***preuves*** de `P` (s'il en existe). Donc montrer `P` dans Lean, c'est construire une
expression/un programme `e` de type `P` (on écrit `e : P`), et le travail de Lean est de vérifier
que cette expression est (1) valide et (2) effectivement de type `P`.

Voici un exemple :
-/

lemma foo {x : ℕ} (h1 : 1 ≤ x) (h3 : x ≤ 3) : 1 ≤ x :=
  h1

/-
Remarquez qu'il n'y a pas de `by` après le `:=`. Ça veut dire qu'on va directement donne
à Lean une expression (on dit un "terme de preuve") de type `1 ≤ x`.
Ici, on donne directement l'hypothèse `h1`.

Remarquez que Lean ne bronche pas si vous remplacez `lemma` par `def`: les deux syntaxes
font fondamentalement la même chose (à des détails pratiques près) : définir une
fonction qui prend des paramètres et renvoie un élément d'un type donné.
En d'autres termes, le lemme `foo` est une ***fonction***, qui prend en paramètre un entier `x`,
une preuve `h1` que `1 ≤ x`, et une preuve `h3` que `x ≤ 3`, et qui vous renvoie une preuve que
`1 ≤ x` (en l'occurence, elle renvoie juste le paramètre `h1`).

Tous les lemmes sont des fonctions de ce genre. Par exemple, le lemme
`Nat.le_antisymm {a : ℕ} {b : ℕ} (h1 : a ≤ b) (h2 : b ≤ a) : a = b` est une fonction,
définie dans la librairie, qui prend en pramètre deux entiers `a` et `b`, puis une preuve
`h1` de type `a ≤ b` et une preuve `h2` que `b ≤ a`, et renvoie une preuve de type `a = b`.
Vous pouvez donc l'utiliser directement comme une fonction :
-/

example {x : ℕ} (h : 1 ≤ x) (h' : 1 ≥ x) : x = 1 :=
  Nat.le_antisymm h' h

/-
Vous vous demandez peut-être où sont passés les deux premiers paramètres :
logiquement, on aurait dû écrire `Nat.le_antisymm x 1 h' h`. En fait, comme les deux paramètres
`{a : ℕ} {b : ℕ} ` sont entre accolades, ils sont *implicites*: Lean devine leur valeur
à partir des paramètres suivants. Le terme de preuve complet est donc :
-/

example {x : ℕ} (h : 1 ≤ x) (h' : 1 ≥ x) : x = 1 :=
  @Nat.le_antisymm x 1 h' h -- `@` veut dire "on donne tous les paramètres explicitement"

/- Un autre lemme utile est `rfl {α : Type*} {x : α} : x = x`, qui montre que n'importe quelle
valeur est égale à elle même. -/

example : 2 = 2 := rfl
example : 2 = 2 := @rfl ℕ 2

/- L'exemple suivant marche car `Lean` peut déplier les définitions de `1`, `2` et `+`
jusqu'à se rendre compte que les deux côtés sont égaux par définition, donc `rfl` est
une preuve valide. -/

example : 1 + 1 = 2 := rfl

/- Du coup, que signifie `by`? Ça indique à Lean "au lieu de donner directement le terme
de preuves, je vais te donner une liste d'instruction sur comment le construire".
Ces instructions sont les *tactiques* : `apply`, `ring`, `calc`, `addarith`, etc...
Les preuves en "mode tactique" sont en général plus facile à écrire, mais Lean travaille
vraiment avec les termes de preuve. -/

/-!
## Partie 2 : "et", "ou"

Pour illustrer tout ce blabla, on va revenir sur les connecteurs "et" et "ou".
Ils sont définis comme des types inductifs, de la manière suivante:
-/

/- Une preuve de `A ∨ B`, c'est soit `Or.inl hA` avec `hA : A`, soit `Or.inl hB` avec `hB : B`.
C'est donc "soit une preuve de `A`, soit une preuve de `B`". -/
inductive Or' (a b : Prop) : Prop
| inl (ha : a) : Or' a b
| inr (hb : b) : Or' a b

/- Une preuve de `A ∧ B` est toujours de la forme `And.intro hA hB` avec `hA : A` et `hB : B`.
C'est donc "une paire formée d'une preuve de `A` et une preuve de `B`". -/
inductive And' (a b : Prop) : Prop
| intro (ha : a) (hb : b) : And' a b

/-
Une fois qu'on sait ça, on peut raisonner avec en utilisant directement la syntaxe `match` et les
constructeurs, comme en programmation fonctionnelle !
-/

example {p q : Prop} (hpq : p ∨ q) : q ∨ p :=
  match hpq with
  | Or.inl hp => Or.inr hp -- Si `hpq` est de la forme `Or.inl hp` avec `hp : P`, on renvoie `Or.inr hp : Q ∨ P`
  | Or.inr hq => Or.inl hq

example {p q : Prop} (hpq : p ∧ q) : q ∧ p :=
  match hpq with
  | And.intro hp hq => And.intro hq hp

/- Comme `And` a un seul constructeur, on peut directement utiliser `⟨hq, hp⟩` au lieu de
`And.intro`...-/
example {p q : Prop} (hpq : p ∧ q) : q ∧ p :=
  match hpq with
  | And.intro hp hq => ⟨hq, hp⟩

/- ... et au lieu de faire `match hpq` on peut directement récupérer les deux composantes
`hpq.1` et `hpq.2`. -/
example {p q : Prop} (hpq : p ∧ q) : q ∧ p :=
  ⟨hpq.2, hpq.1⟩

/- Astuce: Lean est moins interactif quand on écrit les termes de preuve,
mais on peut quand même obtenir de l'aide. Par exemple, pour l'exemple suivant,
vous pouvez d'abord écrire `Or.inl _`, et le message d'erreur vous indiquera ce que
Lean attend à la place du `_`. -/

example {p q : Prop} (h : p ∧ q) : p ∨ q :=
  sorry

example {p q r : Prop} (h : (p ∧ q) ∨ r) : (p ∨ r) ∧ (q ∨ r) :=
  sorry

example {p q r : Prop} (h : (p ∨ r) ∧ (q ∨ r)) : (p ∧ q) ∨ r :=
  sorry

-- lemma eq_zero_or_eq_zero_of_mul_eq_zero {x y : ℝ} (h : x * y = 0) : x = 0 ∨ y = 0
-- lemma eq_of_sub_eq_zero {a b : ℝ} (h : a - b = 0) : a = b

example {x y : ℝ} (h : (x - 1) * (x - 2) = 0) : x = 1 ∨ x = 2 :=
  let fait : x - 1 = 0 ∨ x - 2 = 0 := sorry
  match fait with
  | Or.inl h => sorry
  | Or.inr h => sorry

/-!
## Partie 3 : Implication

Reprenons l'exemple suivant, qui dit que "si `P ∧ Q`, alors `Q ∧ P`".
-/
example {p q : Prop} (hpq : p ∧ q) : q ∧ p :=
  ⟨hpq.2, hpq.1⟩

/-
Une manière équivalente de l'écrire est de dire qu'on a `(P ∧ Q) implique (Q ∧ P)`. Ça s'écrit de la
manière suivante :
-/
example {p q : Prop} : p ∧ q → q ∧ p :=
  fun hpq => ⟨hpq.2, hpq.1⟩

/-
Remarquez que la notation pour les implications est la même que pour les fonctions :
***pour Lean, une preuve de "A implique B", c'est une fonction de type `A → B`***,
c'est à dire qu'elle prend en paramètre une preuve de `A` et renvoie une preuve de `B`.

En fait vous avez déjà utilisé des implications en utilisant des lemmes : il s'agit juste
d'appeler des fonctions. Et pour montrer une implication, on définit une fonction en
utilisant la syntaxe `fun _ => _`.
-/

/- Exemple: si `P => Q` et `Q => R`, alors `P => R`. -/
example {p q r : Prop} (h1 : p → q) (h2 : q → r) : p → r :=
  fun (hp : p) => h2 (h1 hp)

/- Comme les implications sont des fonctions, on peut même utiliser la notation `∘` : -/
example {p q r : Prop} (h1 : p → q) (h2 : q → r) : p → r :=
  h2 ∘ h1

example {p q r : Prop} (H : p → q) : p → (q ∨ r) :=
  sorry

example {p q r : Prop} : (p → (q → r)) → ((p ∧ q) → r) :=
  sorry

example {p q r : Prop} : ((p ∧ q) → r) → (p → (q → r)) :=
  sorry

/-!
## Partie 3 : Récurrence

On a vu comment définir des fonctions par récurrence. Puisque les preuves sont des expressions
comme les autres, la même syntaxe permet de faire des preuves par récurrence !
-/

def somme (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k+1 => (k+1) + somme k

lemma somme_zero : somme 0 = 0 := rfl
lemma somme_succ (k : ℕ) : somme (k+1) = (k+1) + somme k := rfl

lemma somme_eq (n : ℕ) : 2 * somme n = n * (n + 1) :=
  match n with
  | 0 => by -- On repasse en mode tactique, plus pratique pour les calculs
      rw [somme_zero]
  | (k+1) => by
      calc
        2 * somme (k + 1) = 2 * ((k+1) + somme k) := by rw [somme_succ k]
        _ = 2 * (k+1) + 2 * somme k := by ring
        _ = 2 * (k+1) + k * (k+1) := by rw [somme_eq k]
        _ = (k+1) * (k+1+1) := by ring

def somme' (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k+1 => (2*k + 1) + somme' k

lemma somme'_zero : somme' 0 = 0 := rfl
lemma somme'_succ (k : ℕ) : somme' (k+1) = (2*k + 1) + somme' k := rfl

lemma somme'_eq (n : ℕ) : somme' n = n ^ 2 :=
  sorry
