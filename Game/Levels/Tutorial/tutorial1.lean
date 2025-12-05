import Game.Metadata

World "Tutorial"
Level 1

Title "rfl Tutorial"

Introduction "To prove the goal of the form `A = A`, you need to use the `rfl` command. Type `rfl`
in the example below to close the goal."

open mygame Natural

Statement (x q : ℕ) : four * x + q = four * x + q := by
  rfl

NewTactic rfl
