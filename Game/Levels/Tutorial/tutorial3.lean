import Game.Metadata

World "Tutorial"
Level 3

Title "Rewriting definitions"

Introduction "In our game, `one` is defined as `succ zero`, and `two` is defined
as `succ one`. You can type `rewrite [two]` to change `two` to `succ one` in the goal.
To rewrite backwards, you need to type `rewrite [← h]`. To type `←`, use the \\l shortcut.
For example, `rewrite [← one] also works."

open mygame Natural

Statement : two = succ (succ zero) := by
  rewrite [two]
  rewrite [one]
  rfl
