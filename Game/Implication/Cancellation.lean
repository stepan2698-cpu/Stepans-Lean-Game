import Game.Implication.predecessor

open mygame Natural
namespace mygame

World "Cancellation"
Title "Cancellation World"

World "Cancellation"
Level 1

TheoremDoc add_right_cancel as "add_right_cancel"

Statement add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  induction' n with d hd
  · intro h
    rw [add_zero, add_zero] at h
    exact h
  · intro h
    rw [add_succ, add_succ] at h
    have h' := succ_inj _ _ h
    apply hd
    exact h'

/-theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  rw [add_comm n a, add_comm n b]
  exact add_right_cancel a b n

theorem add_left_eq_self (x y : ℕ) : x + y = y → x = zero := by
  nth_rewrite 2 [← zero_add y]
  exact add_right_cancel x zero y

theorem add_right_eq_self (x y : ℕ) : x + y = x → y = zero := by
  nth_rewrite 2 [← add_zero x]
  exact add_left_cancel y zero x

theorem eq_zero_of_add_eq_zero_right (a b : ℕ) : a + b = zero → a = zero := by
  cases' b with d
  · rw [add_zero]
    intro h
    exact h
  · rw [add_succ]
    intro h
    apply succ_ne_zero at h
    cases' h

theorem eq_zero_of_add_eq_zero_left (a b : ℕ) : a + b = zero → b = zero := by
  rw [add_comm]
  exact eq_zero_of_add_eq_zero_right b a

theorem mul_ne_zero (m n : ℕ) : m ≠ zero → n ≠ zero → m * n ≠ zero := by
  intro hm hn
  cases' n with d
  · exfalso
    apply hn
    rfl
  · rw [mul_succ]
    intro h
    apply eq_zero_of_add_eq_zero_left at h
    apply hm
    exact h

theorem pow_ne_zero (a b : ℕ) (ha : a ≠ zero) : a ^ b ≠ zero := by
  induction' b with b' hb'
  · rw [pow_zero]
    exact one_ne_zero
  · rw [pow_succ]
    apply mul_ne_zero
    · exact hb'
    · exact ha

-- This level is quite challenging. You cannot simply prove `n * m = n * k → m = k` by inducting on `k`.
-- What you need to do is to prove the statement `∀ (m : ℕ), n * m = n * k → m = k` by induction
-- instead. You can change your goal to that using the `revert m` command.
-- Alternatively, you can use the `induction' k with d hd generalizing m` command.

theorem mul_left_cancel (n m k : ℕ) (nnez : n ≠ zero) (h : n * m = n * k) : m = k := by
  revert m
  induction' k with d hd
  · intro m h
    rw [mul_zero] at h
    cases' m with m'
    · rfl
    · exfalso
      revert h
      apply mul_ne_zero
      · exact nnez
      · exact succ_ne_zero m'
  · intro m h
    cases' m with m'
    · exfalso
      rw [mul_zero] at h
      symm at h
      revert h
      apply mul_ne_zero
      · exact nnez
      · apply succ_ne_zero
    · rw [mul_succ, mul_succ] at h
      apply add_right_cancel at h
      specialize hd m'
      apply hd at h
      rw [h]

theorem mul_right_cancel (n m k : ℕ) (nnez : n ≠ zero) (h : m * n = k * n) : m = k := by
  rw [mul_comm, mul_comm k] at h
  apply mul_left_cancel at h
  · exact h
  · exact nnez

theorem eq_one_of_mul_eq_left (a b : ℕ) (anez : a ≠ zero) (h : a * b = a) : b = one := by
  nth_rewrite 2 [← mul_one a] at h
  apply mul_left_cancel at h
  · exact h
  · exact anez

theorem eq_one_of_mul_eq_right (a b : ℕ) (bnez : b ≠ zero) (h : a * b = b) : a = one := by
  nth_rewrite 2 [← one_mul b] at h
  apply mul_right_cancel at h
  · exact h
  · exact bnez -/
