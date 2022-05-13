inductive Nat_ where
  | zero : Nat_
  | succ : Nat_ → Nat_
  deriving Repr

namespace Nat_

def add (m n : Nat_) : Nat_ :=
  match n with
  | zero => m
  | succ n => succ (add m n)

-- #eval add (succ (succ zero)) (succ zero)
instance : Add Nat_ where
  add := add

def multiply (m n : Nat_) : Nat_ :=
  match n with
  | zero => zero
  | succ n => m + (multiply m n)

instance : HMul Nat_ Nat_ Nat_ where
  hMul := multiply

#eval multiply (succ (succ zero)) (succ (succ zero))
#eval (succ (succ zero)) * (succ (succ zero))

end Nat_