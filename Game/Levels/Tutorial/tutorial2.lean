import Game.Metadata

World "Tutorial"
Level 2

Title "rewrite Tutorial"

Introduction "To use an assumption of the form `h : A = B`, you can use the `rewrite [h]` command.
In the example below, typing `rewrite [h]` will change `y` to `x + three` in the goal."

open mygame Natural

Statement (x y : ℕ) (h : y = x + three) : two * y = two * (x + three) := by
  rewrite [h]
  rfl

/--If `h : A = B`, then `rewrite [h]` changes all occurences of `A` to `B`.-/
TacticDoc rewrite

NewTactic rewrite
