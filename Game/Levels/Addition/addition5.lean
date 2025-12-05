import Game.Levels.Addition.addition4

World "Addition"
Level 5

Title "Right-associativity of Addition"

open mygame Natural

/--(a + b) + с = (a + c) + b-/
TheoremDoc add_right_comm as "add_right_comm" in "Addition"

Statement add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, add_assoc]
