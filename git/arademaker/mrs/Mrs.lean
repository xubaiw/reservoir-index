
abbrev ℕ := Nat

constant I : Type

structure Constraint where
  lhs : I
  rhs : I

structure EP where
  handle : ℕ 
  predicate : String
  a : List I
  s : List I 
  c : String

structure MRS (α : Type u) where
  gt : I
  index : I
  r : List EP
  i : List Constraint
  c : List Constraint



theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p := 
  λ hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp


