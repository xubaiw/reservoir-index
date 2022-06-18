import Iva.Term

/-
Note that in this file, we assume that the polynomial is sorted with respect
to a monomial ordering, in *decreasing* order.
-/

structure Polynomial (R : Type u) (α : Type v) [BEq α] [Hashable α] :=
(terms : List (Term R α))

namespace Polynomial

variable {R : Type u} {α : Type v} [BEq α] [Hashable α]

def lm? (p : Polynomial R α) : Option (Monomial α) :=
p.terms.head?.map (·.monom)

def lc? (p : Polynomial R α) : Option R :=
p.terms.head?.map (·.coeff)

def lt? (p : Polynomial R α) : Option (Term R α) :=
p.terms.head?

section Inhabited

instance : Inhabited (Polynomial R α) := ⟨⟨[]⟩⟩

def lm (p : Polynomial R α) : Monomial α := p.lm?.get!

variable [Inhabited R]

def lc (p : Polynomial R α) : R := p.lc?.get!

def lt (p : Polynomial R α) : Term R α := p.lt?.get!

end Inhabited

def degree (p : Polynomial R α) : Option (Nat) :=
p.terms.map (·.degree) |>.maximum?

def ofTerm (t : Term R α) : Polynomial R α := ⟨[t]⟩

def ofVar [OfNat R <| nat_lit 1] (a : α) : Polynomial R α := ofTerm (Term.ofVar a)

instance : OfNat (Polynomial R α) <| nat_lit 0 := ⟨⟨[]⟩⟩

section Add

variable [Add R] [BEq R] [OfNat R <| nat_lit 0]

partial def add (p₁ p₂ : Polynomial R α) (o : Monomial α → Monomial α → Bool)
  : Polynomial R α :=
match p₁.terms, p₂.terms with
| _, [] => p₁
| [], _ => p₂
| t :: ts, u :: us =>
  if t.monom == u.monom && t.coeff + u.coeff != 0 then
    ⟨⟨t.coeff + u.coeff, t.monom⟩ :: (add ⟨ts⟩ ⟨us⟩ o).terms⟩
  else if t.monom == u.monom && t.coeff + u.coeff == 0 then
    add ⟨ts⟩ ⟨us⟩ o
  else if o t.monom u.monom then
    ⟨u :: (add p₁ ⟨us⟩ o).terms⟩
  else
    ⟨t :: (add ⟨ts⟩ p₂ o).terms⟩

notation:65 p₁:65 " +[" o "] " p₂:66 => add p₁ p₂ o 

end Add

section HMul

instance : HMul (Monomial α) (Polynomial R α) (Polynomial R α) where
  hMul m p := ⟨p.terms.map (m * ·)⟩

instance [Mul R] : HMul (Term R α) (Polynomial R α) (Polynomial R α) where
  hMul m p := ⟨p.terms.map (m * ·)⟩

instance [Mul R] : HMul R (Polynomial R α) (Polynomial R α) where
  hMul m p := ⟨p.terms.map (m * ·)⟩

end HMul

section Mul

variable [Add R] [BEq R] [OfNat R <| nat_lit 0] [Mul R]

partial def mul (p₁ p₂ : Polynomial R α) (o : Monomial α → Monomial α → Bool)
  : Polynomial R α :=
match p₁.terms, p₂.terms with
| _, [] => 0
| [], _ => 0
| t :: ts, u :: us =>
  ⟨t * u :: (mul ⟨ts⟩ ⟨us⟩ o 
              +[o] t * (⟨us⟩ : Polynomial R α) 
              +[o] u * (⟨ts⟩ : Polynomial R α)).terms⟩

notation:70 p₁:70 " *[" o "] " p₂:71 => mul p₁ p₂ o

end Mul

section Neg

variable [Neg R]

def neg (p : Polynomial R α) : Polynomial R α := ⟨p.terms.map (-·)⟩

instance : Neg (Polynomial R α) := ⟨neg⟩

end Neg

section Sub

variable [Add R] [BEq R] [OfNat R <| nat_lit 0]
variable [Neg R] -- We assume that we have subtraction and negation, and a - b = a + (-b)

def sub (p₁ p₂ : Polynomial R α) (o : Monomial α → Monomial α → Bool) : Polynomial R α :=
add p₁ (neg p₂) o

notation:65 p₁:65 " -[" o "] " p₂:66 => sub p₁ p₂ o

end Sub

instance [BEq R] : BEq (Polynomial R α) := ⟨λ p₁ p₂ => p₁.terms == p₂.terms⟩

instance [OfNat R <| nat_lit 1] : OfNat (Polynomial R α) <| nat_lit 1 := ⟨⟨[1]⟩⟩

section Pow

variable [Add R] [BEq R] [OfNat R <| nat_lit 0] [Mul R] [OfNat R <| nat_lit 1]

def pow (p : Polynomial R α) (o : Monomial α → Monomial α → Bool) : 
  Nat → Polynomial R α
| 0 => 1
| n + 1 => p *[o] pow p o n

notation:76 p:76 " ^[" o "] " n:75 => pow p o n

end Pow

end Polynomial
