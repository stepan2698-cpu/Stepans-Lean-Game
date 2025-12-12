import Game.Implication.implication

open mygame Natural
namespace mygame

World "Predecessor"
Title "Predecessor World"

def pred : ℕ → ℕ
  | zero => zero
  | succ a => a

theorem pred_zero_eq_zero : pred zero = zero := rfl

theorem pred_succ_eq_self (a : ℕ) : pred (succ a) = a := rfl

World "Predecessor"
Level 1

Introduction "In this world, we prove the remaining two Peano axioms (yes, you heard that right!)
in Lean. Firs, we define the 'pred' function as

def pred : ℕ → ℕ

  | zero => zero

  | succ a => a

and start with two theorems 'pred_zero_eq_zero', and 'pred_succ_eq_self'.

Curiously enough, you can prove this level by induction! But in this case, you really don't need the induction assumption ` b ≠ zero → (pred b).succ = b`.
In such cases, you can use `cases' a with b` command instead of induction. This leaves you
with two goals: prove your statement for `zero` and for `succ b`."

/--If a ≠ 0, then succ(pred(a))=a-/
TheoremDoc mygame.succ_pred_eq_self as "succ_pred_eq_self" in "Predecessor"

Statement succ_pred_eq_self (a : ℕ) (nz : a ≠ zero) : succ (pred a) = a := by
  induction' a with b hb
  · exfalso
    apply nz
    rfl
  · rw [pred_succ_eq_self]

example (a : ℕ) (nz : a ≠ zero) : succ (pred a) = a := by
  cases' a with b
  · exfalso
    apply nz
    rfl
  · rw [pred_succ_eq_self]

/--pred(0)=0-/
TheoremDoc mygame.pred_zero_eq_zero as "pred_zero_eq_zero" in "Predecessor"

/--pred(succ(a))=a-/
TheoremDoc mygame.pred_succ_eq_self as "pred_succ_eq_self" in "Predecessor"


World "Predecessor"
Level 2

/--If succ(a) = succ(b), then a = b-/
TheoremDoc mygame.succ_inj as "succ_inj" in "Predeseccor"

Statement succ_inj (a b : ℕ) (h : succ a = succ b) : a = b := by
  rw [← pred_succ_eq_self a, ← pred_succ_eq_self b, h]

World "Predecessor"
Level 3

def is_zero : ℕ → Prop
  | zero => True
  | succ _ => False

-- The statement `True` is true. You can prove `True` by either `exact True.intro` or `trivial`.

/--is_zero zero-/
TheoremDoc mygame.is_zero_zero as "is_zero_zero" in "Predecessor"

theorem is_zero_zero : (is_zero zero) := by
  rw [is_zero]
  trivial

/--¬ is_zero (succ n)-/
TheoremDoc mygame.not_is_zero_of_succ as "not_is_zero_of_succ" in "Predecessor"

theorem not_is_zero_of_succ (n : ℕ) : (¬ is_zero (succ n)) := by
  rw [is_zero]
  intro h
  exact h

Introduction "In this level, we define a function is_zero by

def is_zero : ℕ → Prop

  | zero => True

  | succ _ => False

We have two new theorems 'is_zero_zero' and 'not_is_zero_of_succ'."

/--succ n ≠ 0-/
TheoremDoc mygame.succ_ne_zero as "succ_ne_zero" in "Predecessor"

Statement succ_ne_zero (n : ℕ) : (succ n ≠ zero) := by
  intro h
  apply not_is_zero_of_succ n
  rw [h]
  exact is_zero_zero

World "Predecessor"
Level 4

/--0 ≠ succ(n)-/
TheoremDoc mygame.zero_ne_succ as "zero_ne_succ" in "Predecessor"

Statement zero_ne_succ (n : ℕ) : (zero ≠ succ n) := by
  intro h
  symm at h
  exact succ_ne_zero n h

World "Predecessor"
Level 5

/--0 ≠ 1-/
TheoremDoc mygame.zero_ne_one as "zero_ne_one" in "Predecessor"

Statement zero_ne_one : (zero ≠ one) := by
  rw [one]
  apply zero_ne_succ

World "Predecessor"
Level 6

/--1 ≠ 0-/
TheoremDoc mygame.one_ne_zero as "one_ne_zero" in "Predecessor"

Statement one_ne_zero : (one ≠ zero) := by
  rw [one]
  apply succ_ne_zero
