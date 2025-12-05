import Game.Metadata
import Game.Levels.Tutorial.tutorial5

World "Tutorial"
Level 6

Title "Two plus two is four"

Introduction "The `rewrite [h : A = B]` command instructs Lean to change **all** instances of `A` in the
goal to `B`. If you have two instances of `A`, and would like to change only one of them to
`B`, you can instruct Lean to do so by typing either `nth_rewrite 1 [h]` or `nth_rewrite 2 [h]`."

open mygame Natural

/--2 + 2 = 4-/
TheoremDoc two_plus_two_eq_four as "two_plus_two_eq_four" in "Addition"

Statement two_plus_two_eq_four : two + two = four := by
  nth_rewrite 2 [two]
  rewrite [add_succ]
  rewrite [← add_one]
  rewrite [four]
  rewrite [three]
  rfl

NewHiddenTactic nth_rewrite
