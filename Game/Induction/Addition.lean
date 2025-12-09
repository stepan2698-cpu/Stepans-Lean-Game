import Game.Induction.Tutorial

open mygame Natural

World "Addition"
Title "Addition World"

World "Addition" Level 1

Title "Adding zero from the left"

Introduction "To prove this next theorem, you need to use induction. This is done by using the command
`induction' a with d hd`, where `a` is the variable you want to do induction on. This
creates two subgoals:
Goal 1: `zero + zero = zero` -- prove the base case of the induction.
Goal 2 : `d : ℕ`
          `hd : zero + d = d`
          `⊢ zero + d.succ = d.succ` -- prove the induction step.
As you can see, `d` and `hd` are just arbitrary names you give to the variable in the
induction step and the induction assumption.

You can also use `rw [h]` instead of `rewrite [h]`. `rw` is the better version of `rewrite`
in that `rw` tries to apply `rfl` automatically after rewriting. This makes the code shorter."

/--0 + a = a-/
TheoremDoc zero_add as "zero_add"

Statement zero_add (a : ℕ) : zero + a = a := by
  induction' a with d hd
  · rfl
  · rw [add_succ, hd]

NewTactic induction' rw

World "Addition" Level 2

Title "Adding successor from the left"

open mygame Natural

/--succ(a) + b = succ(a + b)-/
TheoremDoc succ_add as "succ_add" in "Addition"

Statement succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction' b with d hd
  · rfl
  · rw [add_succ, hd, add_succ]

World "Addition" Level 3

Title "Commutativity of Addition"

open mygame Natural

/--a + b = b + a-/
TheoremDoc add_comm as "add_comm" in "Addition"

Statement add_comm (a b : ℕ) : a + b = b + a := by
  induction' b with d hd
  · rw [add_zero, zero_add]
  · rw [add_succ, hd, succ_add]

World "Addition" Level 4

Title "Associativity of Addition"

open mygame Natural

/--a + b = b + a-/
TheoremDoc add_assoc as "add_assoc" in "Addition"

Statement add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction' c with d hd
  · rfl
  · rw [add_succ, hd, add_succ, add_succ]

World "Addition" Level 5

Title "Right-associativity of Addition"

open mygame Natural

/--(a + b) + с = (a + c) + b-/
TheoremDoc add_right_comm as "add_right_comm" in "Addition"

Statement add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, add_assoc]

World "Addition"
Level 6

Title "Left-associativity of Addition"

open mygame Natural

/--(a + b) + с = (a + c) + b-/
TheoremDoc add_left_comm as "add_left_comm" in "Addition"

Statement add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]
