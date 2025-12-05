import Game.Levels.Addition

open mygame Natural

World "Multiplication"
Title "Multiplication World"

World "Multiplication" Level 1

Title "Multiplication by one from the right"

Introduction "Multiplication on the natural numbers is defined by
 def mul : ℕ → ℕ → ℕ
   | _, zero => zero
   | a, succ b => add (mul a b) a
Therfore, theorems `mul_zero` and `mul_succ` are true by definition."

/--a * 1 = a-/
TheoremDoc mul_one as "mul_one" in "Multiplication"

Statement mul_one (a : ℕ) : a * one = a := by
  rw [one, mul_succ, mul_zero, zero_add]

/--a * 0 = 0-/
TheoremDoc mygame.mul_zero as "mul_zero" in "Multiplication"

/--a * succ(b) = a * b + a-/
TheoremDoc mygame.mul_succ as "mul_succ" in "Multiplcation"

NewTheorem mygame.mul_zero mygame.mul_succ

World "Multiplication" Level 2

Title "Multiplication by zero from the left"

/--0 * a = 0-/
TheoremDoc zero_mul as "zero_mul" in "Multiplication"

Statement zero_mul (a : ℕ) : zero * a = zero := by
  induction' a with d hd
  · rfl
  · rw [mul_succ, add_zero, hd]

World "Multiplication" Level 3

Title "Multiplication by the successor from the left"

/--succ(a) * b = a * b + b-/
TheoremDoc succ_mul as "succ_mul" in "Multiplication"

Statement succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  induction' b with d hd
  · rfl
  · rw [mul_succ, hd, mul_succ, add_one, add_one]
    rw [add_assoc, add_assoc, add_left_comm d a one]

World "Multiplication" Level 4

Title "Commutativity of Multiplication"

/--a * b = b * a-/
TheoremDoc mul_comm as "mul_comm" in "Multiplication"

Statement mul_comm (a b : ℕ) : a * b = b * a := by
  induction' b with d hd
  · rw [zero_mul, mul_zero]
  · rw [succ_mul, mul_succ, hd]

World "Multiplication" Level 5

Title "Multiplication by one from the left"

/--1 * a = a-/
TheoremDoc one_mul as "one_mul" in "Multiplcation"

Statement one_mul (a : ℕ): one * a = a := by
  rw [mul_comm, mul_one]

World "Multiplication" Level 6

Title "Multiplication by two from the right"

/--a * 2 = a + a-/
TheoremDoc mul_two as "mul_two" in "Multiplcation"

Statement mul_two (a : ℕ) : a * two = a + a := by
  rw [two, mul_succ, mul_one]

World "Multiplication" Level 7

Title "Multiplication by two from the right"

/--2 * a = a + a-/
TheoremDoc two_mul as "two_mul" in "Multiplication"

Statement two_mul (a : ℕ) : two * a = a + a := by
  rw [mul_comm, mul_two]

World "Multiplication" Level 8

Title "Right distributivity of multiplication"

/--(a + b) * c = a * c + b * c-/
TheoremDoc add_mul as "add_mul" in "Multiplication"

Statement add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  induction' c with d hd
  · rfl
  · rw [mul_succ, mul_succ, mul_succ, hd]
    rw [add_assoc, add_assoc, add_left_comm a]

World "Multiplication" Level 9

Title "Left distributiviy of multiplication"

/--a * (b + c) = a * b + a * c-/
TheoremDoc mul_add as "mul_add" in "Multiplication"

Statement mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  rw [mul_comm a, mul_comm a, mul_comm a, add_mul]

World "Multiplication" Level 10

Title "Associativity of multiplication"

/--(a * b) * c = a * (b * c)-/
TheoremDoc mul_assoc as "mul_assoc" in "Multiplication"

Statement mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := by
  induction' c with d hd
  · rw [mul_zero, mul_zero, mul_zero]
  · rw [mul_succ, mul_succ, mul_add, hd]

World "Multiplication" Level 11

Title "Right-commutativity of multiplication"

/--(a * b) * c = (a * c) * b-/
TheoremDoc mul_right_comm as "mul_right_comm" in "Multiplication"

Statement mul_right_comm (a b c : ℕ) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b, mul_assoc]

World "Multiplication" Level 12

Title "Left-commutativity of multiplication"

/--a * (b * c) = b * (a * c)-/
TheoremDoc mul_left_comm as "mul_left_comm" in "Multiplication"

Statement mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a, mul_assoc]
