import Game.Levels.Addition.addition1

World "Addition"
Level 2

Title "Adding successor from the left"

open mygame Natural

/--succ(a) + b = succ(a + b)-/
TheoremDoc succ_add as "succ_add" in "Addition"

Statement succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction' b with d hd
  · rfl
  · rw [add_succ, hd, add_succ]
