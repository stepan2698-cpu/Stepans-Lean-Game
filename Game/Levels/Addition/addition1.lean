import Game.Metadata

World "Addition"
Level 1

Title "Adding zero from the left"

Introduction "To prove this next theorem, you need to use induction. This is done by using the command
`induction' a with d hd`, where `a` is the variable you want to do induction on. This
creates two subgoals:
Goal 1: `zero + zero = zero` -- prove the base case of the induction.
Goal 2 : `d : ℕ`
          `hd : zero + d = d`
          `⊢ zero + d.succ = d.succ` -- prove the induction step.
As you can see, `d` and `hd` are just arbitrary names you give to the variable in the
induction step and the induction assumption.

You can also use `rw [h]` instead of `rewrite [h]`. `rw` is the better version of `rewrite`
in that `rw` tries to apply `rfl` automatically after rewriting. This makes the code shorter."

open mygame Natural

Statement zero_add (a : ℕ) : zero + a = a := by
  induction' a with d hd
  · rfl
  · rw [add_succ, hd]

NewTactic induction'
