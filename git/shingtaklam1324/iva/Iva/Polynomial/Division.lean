import Iva.Polynomial

namespace Polynomial
/-
The division algorithm for k[x₁, ..., xₙ] of f by f₁, ..., fₖ
-/

variable {α : Type u} {R : Type v}
variable [BEq α] [Hashable α]
variable [Add R] [BEq R] [OfNat R <| nat_lit 0] [Mul R] [Neg R] [Div R]
variable [Dvd R] [Inhabited R]

def divisionStep 
  (p : Polynomial R α)
  (fs : List (Polynomial R α))
  (qs : List (Polynomial R α))
  (o : Monomial α → Monomial α → Bool) :
  Polynomial R α × List (Polynomial R α) × Bool :=
match fs, qs with
| [], _ => (p, qs, false)
| _, [] => (p, qs, false)
| f :: fss, q :: qss => 
  if f.lt ∣ p.lt then
    let p' := p -[o] (p.lt / f.lt) * f
    let q' := q +[o] Polynomial.ofTerm (p.lt / f.lt)
    (p', q' :: qss, true)
  else
    let (p', qs', b) := divisionStep p fss qss o
    (p', q :: qs', b)

partial def divisionAux
  (p : Polynomial R α)
  (fs : List (Polynomial R α))
  (qs : List (Polynomial R α))
  (r : Polynomial R α)
  (o : Monomial α → Monomial α → Bool) :
  Polynomial R α × List (Polynomial R α) × Polynomial R α :=
if p == 0 then
  (p, qs, r)
else
  let (p', qs', divOcc) := divisionStep p fs qs o
  divisionAux (if divOcc then p' else p' -[o] Polynomial.ofTerm p'.lt) 
              fs 
              qs' 
              (if divOcc then r else r +[o] Polynomial.ofTerm p'.lt)
              o

def division 
  (p : Polynomial R α) 
  (fs : List (Polynomial R α)) 
  (o : Monomial α → Monomial α → Bool) : 
  List (Polynomial R α) × Polynomial R α :=
(divisionAux p fs (fs.map λ _ => 0) 0 o).2

def quot
  (p : Polynomial R α)
  (fs : List (Polynomial R α))
  (o : Monomial α → Monomial α → Bool) :
  List (Polynomial R α) :=
(division p fs o).1

def rem
  (p : Polynomial R α)
  (fs : List (Polynomial R α))
  (o : Monomial α → Monomial α → Bool) :
  Polynomial R α :=
(division p fs o).2

end Polynomial
