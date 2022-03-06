import Lean4Axiomatic.Eqv

open Relation (EqvOp)

namespace AA

class Commutative {α : Sort u} {β : Sort v} [EqvOp β] (f : α → α → β) where
  comm {x y : α} : f x y ≃ f y x

export Commutative (comm)

end AA
