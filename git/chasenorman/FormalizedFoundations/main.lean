def Identifier := Nat

structure Clause where
  head: Identifier
  body: List Clause