import Game.Levels.Addition.addition3

World "Addition"
Level 4

Title "Associativity of Addition"

open mygame Natural

/--a + b = b + a-/
TheoremDoc add_assoc as "add_assoc" in "Addition"

Statement add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction' c with d hd
  · rfl
  · rw [add_succ, hd, add_succ, add_succ]
