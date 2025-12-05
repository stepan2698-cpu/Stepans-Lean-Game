import Game.Levels.Addition.addition5

World "Addition"
Level 6

Title "Left-associativity of Addition"

open mygame Natural

/--(a + b) + с = (a + c) + b-/
TheoremDoc add_left_comm as "add_left_comm" in "Addition"

Statement add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]
