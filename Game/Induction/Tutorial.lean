import Game.Metadata

World "Tutorial"
Title "Tutorial"

Introduction "This is a tutorial world introducing basic Lean tactics."

World "Tutorial" Level 1

Title "rfl Tutorial"

Introduction "To prove the goal of the form `A = A`, you need to use the `rfl` command. Type `rfl`
in the example below to close the goal."

open mygame Natural

Statement (x q : ℕ) : four * x + q = four * x + q := by
  rfl

NewTactic rfl

World "Tutorial" Level 2

Title "rewrite Tutorial"

Introduction "To use an assumption of the form `h : A = B`, you can use the `rewrite [h]` command.
In the example below, typing `rewrite [h]` will change `y` to `x + three` in the goal."

open mygame Natural

Statement (x y : ℕ) (h : y = x + three) : two * y = two * (x + three) := by
  rewrite [h]
  rfl

NewTactic rewrite

World "Tutorial" Level 3

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

World "Tutorial" Level 4

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
TheoremDoc mygame.add_zero as "add_zero" in "Addition"

NewTheorem mygame.add_zero

World "Tutorial" Level 5

Title "Adding one"

open mygame Natural

/--succ a = a + 1-/
TheoremDoc add_one as "add_one" in "Addition"

Statement add_one (a : ℕ) : succ a = a + one := by
  rewrite [one]
  rewrite [add_succ]
  rewrite [add_zero]
  rfl

World "Tutorial" Level 6

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
