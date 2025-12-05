import Game.Metadata

World "Tutorial"
Level 4

Title "Rewriting theorems"

Introduction "This is our first theorem, `add_zero`. A theorem is like an assumption that is always
available. If you type `rewrite [add_zero]`, Lean will find the first instance of
the expression `something + zero` in the goal and change it to `something`.
You can also instruct Lean to rewrite the specific instance of `add_zero` which you want.
For example, `add_zero c` is the name for the equality `c + zero = zero`. Typing
`rewrite [add_zero c]` will instruct Lean to find specifically the expression `c + zero`
and change it to `c`."

open mygame Natural

Statement (a b c : ℕ) : a + (b + zero) + (c + zero) = a + b + c := by
  rewrite [add_zero c]
  rewrite [add_zero b]
  rfl

/--a + 0 = a-/
TheoremDoc mygame.add_zero as "add_zero"

NewTheorem mygame.add_zero
