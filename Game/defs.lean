import Lean
import Batteries
open Lean Elab Tactic Meta Parser.Tactic

namespace mygame

inductive Natural where
| zero : Natural
| succ : Natural → Natural

open Natural

notation (priority := 1000000) "ℕ" => Natural

def one : ℕ := succ zero
def two : ℕ := succ one
def three : ℕ := succ two
def four : ℕ := succ three

def add : ℕ → ℕ → ℕ
  | a, zero => a
  | a, succ b => succ (add a b)

instance : Add ℕ :=
  { add := add }

def mul : ℕ → ℕ → ℕ
  | _, zero => zero
  | a, succ b => add (mul a b) a

instance : Mul ℕ :=
  { mul := mul }

def pow : ℕ → ℕ → ℕ
  | _, zero => one
  | a, succ b => mul (pow a b) a

instance : HPow ℕ ℕ ℕ :=
  { hPow := pow }

theorem add_zero (a : ℕ) : a + zero = a := rfl

theorem add_succ (a b : ℕ) : (a + succ b = succ (a + b)) := rfl

theorem mul_zero (a : ℕ) : a * zero = zero := rfl

theorem mul_succ (a b : ℕ) : a * b.succ = a * b + a := rfl

theorem pow_zero (a : ℕ) : a ^ zero = one := rfl

theorem pow_succ (a b : ℕ) : a ^ (succ b) = a ^ b * a := rfl

macro "nth_rewrite" c:optConfig ppSpace nums:(num)+ s:rwRuleSeq loc:(location)? : tactic => do
  `(tactic| rewrite $[$(getConfigItems c)]* (occs := .pos [$[$nums],*]) $s:rwRuleSeq $(loc)?)

macro "induction'" a:Lean.Parser.Tactic.elimTarget "with" d:ident hd:ident : tactic => do
  `(tactic|
    induction $a with
    | zero => ?_
    | succ $d $hd => ?_
  )
