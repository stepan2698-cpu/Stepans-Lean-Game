import Game.Levels.Addition.addition6

World "Multiplication"
Title "Multiplication World"

World "Multiplication"
Level 1

Introduction "Multiplication on the natural numbers is defined by
 def mul : ℕ → ℕ → ℕ
   | _, zero => zero
   | a, succ b => add (mul a b) a
Therfore, theorems `mul_zero` and `mul_succ` are true by definition."

open mygame Natural

/--a * 1 = a-/
TheoremDoc mul_one as "mul_one" in "Multiplication"

Statement mul_one (a : ℕ) : a * one = a := by
  rw [one, mul_succ, mul_zero, zero_add]

/--a * 0 = 0-/
TheoremDoc mygame.mul_zero as "mul_zero" in "Multiplication"

/--a * succ(b) = a * b + a-/
TheoremDoc mygame.mul_succ as "mul_succ" in "Multiplcation"

NewTheorem mygame.mul_zero mygame.mul_succ

World "Multiplication"
Level 2

/--0 * a = 0-/
TheoremDoc zero_mul as "zero_mul" in "Multiplication"

Statement zero_mul (a : ℕ) : zero * a = zero := by
  induction' a with d hd
  · rfl
  · rw [mul_succ, add_zero, hd]

World "Multiplication"
Level 3

/--succ(a) * b = a * b + b-/
TheoremDoc succ_mul as "succ_mul" in "Multiplication"

Statement succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  induction' b with d hd
  · rfl
  · rw [mul_succ, hd, mul_succ, add_one, add_one]
    rw [add_assoc, add_assoc, add_left_comm d a one]

World "Multiplication"
Level 4
/--a * b = b * a-/
TheoremDoc mul_comm as "mul_comm" in "Multiplication"

Statement mul_comm (a b : ℕ) : a * b = b * a := by
  induction' b with d hd
  · rw [zero_mul, mul_zero]
  · rw [succ_mul, mul_succ, hd]
