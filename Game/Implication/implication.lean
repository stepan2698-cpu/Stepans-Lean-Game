import Game.Induction.Exponentiation

open mygame Natural

World "Implication"
Title "Implication World"

World "Implication" Level 1

Introduction "Another way to use assumptions is the `exact` command. If your goal is the same as one
of your assumptions, you can use the `exact` command to finish the proof. For example,
you can type `exact h1` in the example below."

NewTactic exact

Statement (x y z : ℕ) (h1 : x + y = two * z) (h2 : three * x + z = y) : x + y = two * z := by
  exact h1

World "Implication" Level 2

Introduction "You can do rewriting inside you assumtion by using the `at` keyword. Type `rw [zero_add] at h`
to instruct Lean to find the pattern `something + zero` inside the assumption h."

Statement (x y : ℕ) (h : zero + x = zero + y + two) : x = y + two := by
  rw [zero_add, zero_add] at h
  exact h

World "Implication" Level 3

Statement (x y : ℕ) (h : x = y) : y = x := by
  rw [h]

World "Implication" Level 4

Introduction "You can use the `symm` command to flip statements from `A = B` to `B = A`. Type `symm`
to do this to the goal, or `symm at h` to do this at the assumption h."

Statement (x y z : ℕ) (h1 : x = y) (h2 : y = z) : z = x := by
  symm
  rw [h1, h2]

NewTactic symm

World "Implication" Level 5

Introduction "Lean denotes the statement 'If P, then Q' by `P → Q`. You can type → by using the \r shortcut.
To use an assumption of the form `P → Q`, you can use the `apply` command. This command has
two modes:

First, if your goal is `Q`, and `h : P → Q` is known, you can type `apply h`, which will change
your goal to `P`.

Second, if `h1 : P` and `h2 : P → Q` are assumptions, you can type `apply h2 at h1` to
change the assumption `h1` to `Q`.

There's also a third way to apply statements, which is the shortest, but also the hardest to read.
If `h1 : P` and `h2 : P → Q` are any statements, you can use `h2 h1` to get the statement `Q`.
That is, `h2 : P → Q` can be intepreted as a function from proofs of `P` to proofs of `Q`.
If `h1 : P` is a proof of `P`, and `h2 : P → Q` is a function from proofs of `P` to proofs of `Q`,
then, naturally, `h2 h1` is a proof of `Q`."

Statement (P Q : Prop) (h1 : P) (h2 : P → Q) : Q := by
  apply h2
  exact h1

NewTactic apply

World "Implication" Level 6

Statement (P Q R S T U: Prop) (p : P) (h : P → Q) (i : Q → R) (j : Q → T) (k : S → T) (l : T → U) : U := by
  apply l
  apply j
  apply h
  exact p

World "Implication" Level 7

Introduction "To prove the goal of type `P → Q`, you need to mimic the 'Assume P. Then Q' structure in
the natural language proof. You can do that by typing `intro h`. This will change the goal
to `Q` and add `h : P` to the list of your assumptions. Here `h` is just an arbitrary name
you can give ti the assumption."

NewTactic intro

Statement imp_refl (P : Prop) : P → P := by
  intro h
  exact h

World "Implication" Level 8

Statement imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro h k p
  apply k
  apply h
  exact p

World "Implication" Level 9

Introduction "If you want to prove a statement as an intermediate step, you can use the `have` command.
Type `have h : P := by` and indent the code to the right to temporarily change your goal
to P. After you finish the proof, `h : P` will be added to the list of your assumptions.

You can also just use `apply h` in this situation, which will leave you with two hanging goals."

Statement (P Q R : Prop) : (P → Q → R) → (P → Q) → P → R := by
  intro h k p
  have l : Q → R := by
    apply h
    exact p
  apply l
  apply k
  exact p
