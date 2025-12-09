import Game.Induction.Multiplication

open mygame Natural

World "Exponnetiation"
Title "Exponentiation World"

Introduction "Exponentiation on the natural numbers is defined by
def pow : ℕ → ℕ → ℕ
  | _, zero => one
  | a, succ b => mul (pow a b) a
 Hence, we also start with two results which are true by definition."

/--a ^ 0 = 1-/
TheoremDoc pow_zero as "pow_zero" in "Exponentiation"

/--a ^ (succ(b)) = a ^ b * a-/
TheoremDoc pow_succ as "pow_succ" in "Exponentiation"

World "Exponentiation" Level 1

/--0 ^ (succ(m)) = 0-/
TheoremDoc zero_pow_succ as "zero_pow_succ" in "Exponentiation"

Statement zero_pow_succ (m : ℕ) : zero ^ (succ m) = zero := by
  rw [pow_succ, mul_zero]

World "Exponentiation" Level 2

/--a ^ 1 = a-/
TheoremDoc pow_one as "pow_one" in "Exponentiation"

Statement pow_one (a : ℕ) : a ^ one = a := by
  rw [one, pow_succ, pow_zero, one_mul]

World "Exponentiation" Level 3

/--1 ^ a = 1-/
TheoremDoc one_pow as "one_pow" in "Exponentiation"

Statement one_pow (a : ℕ) : one ^ a = one := by
  induction' a with d hd
  · rfl
  · rw [pow_succ, mul_one, hd]

World "Exponentiation" Level 4

/--a ^ 2 = a * a-/
TheoremDoc pow_two as "pow_two" in "Exponentiation"

Statement pow_two (a : ℕ) : a ^ two = a * a := by
  rw [two, pow_succ, pow_one]

World "Exponentiation" Level 5

/--a ^ (m + n) = a ^ m * a ^ n-/
TheoremDoc pow_add as "pow_add" in "Exponentiation"

Statement pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction' n with d hd
  · rw [add_zero, pow_zero, mul_one]
  · rw [add_succ, pow_succ, hd, pow_succ, mul_assoc]

World "Exponentiation" Level 6

/--(a * b) ^ n = a ^ n * b ^ n -/
TheoremDoc mul_pow as "mul_pow" in "Exponentiation"

Statement mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction' n with d hd
  · rw [pow_zero, pow_zero, pow_zero, mul_one]
  · rw [pow_succ, pow_succ, pow_succ, hd]
    rw [mul_assoc, mul_assoc, mul_left_comm a]

World "Exponentiation" Level 7

/--a ^ (m * n) = (a ^ m) ^ n-/
TheoremDoc pow_mul as "pow_mul" in "Exponentiation"

Statement pow_mul (a m n : ℕ) : a ^ (m * n) = (a ^ m) ^ n := by
  induction' n with d hd
  · rw [mul_zero, pow_zero, pow_zero]
  · rw [mul_succ, pow_add, hd, pow_succ]

World "Exponentiation" Level 8

/--(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2-/
TheoremDoc add_pow_two as "add_pow_two" in "Exponentiation"

Statement add_pow_two (a b : ℕ) : (a + b) ^ two = a ^ two + two * a * b + b ^ two := by
  rw [pow_two, pow_two, pow_two, add_mul, mul_add, mul_add]
  rw [add_assoc, ← add_assoc (a * b), mul_comm b a, ← two_mul, add_assoc, mul_assoc]
