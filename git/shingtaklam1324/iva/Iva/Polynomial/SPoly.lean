import Iva.Polynomial

variable {α : Type u} {R : Type v}
variable [BEq α] [Hashable α]
variable [Add R] [BEq R] [OfNat R <| nat_lit 0] [Mul R] [Neg R] [Div R] 
variable [Inhabited R] [OfNat R <| nat_lit 1]

namespace Polynomial

def sPoly (p q : Polynomial R α) (o : Monomial α → Monomial α → Bool) : 
  Polynomial R α :=
let m := p.lm.lcm q.lm
(Term.ofMonomial m / p.lt) * p -[o] (Term.ofMonomial m / q.lt) * q

end Polynomial
