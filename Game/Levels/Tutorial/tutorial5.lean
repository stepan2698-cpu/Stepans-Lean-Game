import Game.Metadata

World "Tutorial"
Level 5

Title "Adding one"

open mygame Natural

/--succ a = a + 1-/
TheoremDoc add_one as "add_one" in "Addition"

Statement add_one (a : ℕ) : succ a = a + one := by
  rewrite [one]
  rewrite [add_succ]
  rewrite [add_zero]
  rfl
