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
