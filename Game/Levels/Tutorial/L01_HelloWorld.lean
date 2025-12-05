import Game.Metadata
import Game.defs

World "Tutorial"
Level 1

Title "rfl Tutorial"

Introduction "To prove the goal of the form `A = A`, you need to use the `rfl` command. Type `rfl`
in the example below to close the goal."

open mygame

Statement (x q : ℕ) : four * x + q = four * x + q := by
  rfl

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
