import Game.Levels.Addition.addition2

World "Addition"
Level 3

Title "Commutativity of Addition"

open mygame Natural

/--a + b = b + a-/
TheoremDoc add_comm as "add_comm" in "Addition"

Statement add_comm (a b : ℕ) : a + b = b + a := by
  induction' b with d hd
  · rw [add_zero, zero_add]
  · rw [add_succ, hd, succ_add]
