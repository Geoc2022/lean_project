import Mathlib.Tactic

/- For a bit of the intro we'll be using Surreal Numbers: How Two Ex-Students Turned On To Pure Mathematics And Found Total Happiness: A Mathematical Novelette -/

/- # Creations of Axioms
In the beginning, everything was void, and J. H. W. H. Conway began to create numbers. Conway said, "Let there be two rules which bring forth all numbers large and small.
-/

def surreal : Type := sorry
namespace surreal

def le: surreal → surreal → Prop := sorry

def lex (X Y : Set surreal) : Prop := ∀ x ∈ X, ∀ y ∈ Y, le x y

/-
## Rule 1
Every number corresponds to two sets of previously created numbers, such that no member of the left set is greater than or equal to any member of the right set.
-/

def left : surreal → Set surreal := sorry
def right : surreal → Set surreal := sorry

axiom surreal.rule1 (x : surreal) : ∀ (y : surreal), ¬ (y ∈ left x ∧ y ∈ right x)
def is_surreal (x : surreal) : Prop := ∀ (y : surreal), ¬ (y ∈ left x ∧ y ∈ right x)

axiom surreal.rule1_lex (s : surreal) (X Y : Set surreal) : left s = X → right s = Y → lex X Y




/-
## Rule 2
And the second rule shall be this: One number is less than or equal to another number if and only if no member of the first number's left set is greater than or equal to the second number, and no member of the second number's right set is less than or equal to the first number."
-/

axiom surreal.rule2 (x y : surreal) : (le x y) ↔
  (∀ (a : surreal), a ∈ left x → ¬ (le a y)) ∧
  (∀ (b : surreal), b ∈ right y → ¬ (le x b))


/-
## Creation of the Numbers
The first number was created from the void left set and the void right set. Conway called this number "zero"
-/

def zero : surreal := sorry
axiom zero.has_left: zero.left = {}
axiom zero.has_right: zero.right = {}
lemma zero.is_surreal : is_surreal zero := by
  intro z
  rw [zero.has_left]
  rw [zero.has_right]
  simp


/-
# The First Day
On the first day of creation, Conway "proves" that 0 =< O-/

lemma zero_le_zero : le zero zero := by
  rw [surreal.rule2]
  apply And.intro

  intro a
  rw [zero.has_left]
  simp

  intro b
  rw [zero.has_right]
  simp

/-
# The Second Day
On the next day, two more numbers were created, one with zero as its left set and one with zero as its right set. And Conway called the former number "one," and the latter he called "minus one."
-/
def one : surreal := sorry
axiom one.has_left: one.left = {zero}
axiom one.has_right: one.right = {}
lemma one.is_surreal : is_surreal one := by
  intro o
  rw [one.has_left]
  rw [one.has_right]
  simp

def minus_one : surreal := sorry
axiom minus_one.has_left: minus_one.left = {}
axiom minus_one.has_right: minus_one.right = {zero}
lemma minus_one.is_surreal : is_surreal minus_one := by
  intro o
  rw [minus_one.has_left]
  rw [minus_one.has_right]
  simp

lemma zero_le_one : le zero one := by
  rw [surreal.rule2]
  apply And.intro

  intro a
  rw [zero.has_left]
  simp

  intro b
  rw [one.has_right]
  simp

lemma minus_one_le_zero : le minus_one zero := by
  rw [surreal.rule2]
  apply And.intro

  intro a
  rw [minus_one.has_left]
  simp

  intro b
  rw [zero.has_right]
  simp

lemma not_le_to_not_eq_zero_minus_one: ¬(le zero minus_one) → ¬(zero = minus_one) :=
  by
    intro h1
    intro h2
    apply h1
    rw [h2]
    apply zero_le_zero

lemma not_le_to_not_eq_one_zero: ¬(le one zero) → ¬(one = zero) :=
  by
    intro h1
    intro h2
    apply h1
    rw [h2]
    apply minus_one_le_zero

/-
# Evening of the Second Day
-/
def n_plus_one : surreal → surreal := sorry
axiom n_plus_one.has_left (n : surreal) : (n_plus_one n).left = n.left ∪ {n}
axiom n_plus_one.has_right (n : surreal) : (n_plus_one n).right = {}
lemma n_plus_one.is_surreal (n : surreal) : is_surreal (n_plus_one n) := by
  intro x
  rw [n_plus_one.has_left]
  rw [n_plus_one.has_right]
  simp

def n_minus_one : surreal → surreal := sorry
axiom n_minus_one.has_left (n : surreal) : (n_minus_one n).left = {}
axiom n_minus_one.has_right (n : surreal) : (n_minus_one n).right = n.right ∪ {n}
lemma n_minus_one.is_surreal (n : surreal) : is_surreal (n_minus_one n) := by
  intro x
  rw [n_minus_one.has_left]
  rw [n_minus_one.has_right]
  simp
