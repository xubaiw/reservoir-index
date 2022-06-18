import Iva.Polynomial.SPoly
import Iva.Polynomial.Division
import Iva.Data.List

variable {α : Type u} {R : Type v}
variable [BEq α] [Hashable α]
variable [Add R] [BEq R] [OfNat R <| nat_lit 0] [Mul R] [Neg R] [Div R]
variable [Dvd R] [Inhabited R] [OfNat R <| nat_lit 1]

open Polynomial

def buchbergerCriterion
  (F : List (Polynomial R α)) (o : Monomial α → Monomial α → Bool) : Bool :=
F.pairs.all λ (f, g) => rem (sPoly f g o) F o == 0

partial def buchberger 
  (F : List (Polynomial R α)) 
  (o : Monomial α → Monomial α → Bool) : 
  List (Polynomial R α) :=
let G := F.pairs.foldl (init := F) λ l (f, g) =>
  let r := rem (sPoly f g o) F o
  if r == 0 then l else l ++ [r]
if G == F then
  G
else
  buchberger G o
