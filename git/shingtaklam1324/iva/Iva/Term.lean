import Iva.Monomial

open Std

structure Term (R : Type u) (α : Type v) [BEq α] [Hashable α] :=
(coeff : R)
(monom : Monomial α)

namespace Term

variable {R : Type u} {α : Type v} [BEq α] [Hashable α]

def degree (t : Term R α) : Nat := t.monom.degree

def exponent (t : Term R α) (a : α) : Nat := t.monom.exponent a

def variables (t : Term R α) : HashSet α := t.monom.variables

instance [Mul R] : Mul (Term R α) where
  mul t₁ t₂ := ⟨t₁.coeff * t₂.coeff, t₁.monom * t₂.monom⟩

instance [Mul R] : HMul R (Term R α) (Term R α) where
  hMul r t := ⟨r * t.coeff, t.monom⟩

instance : HMul (Monomial α) (Term R α) (Term R α) where
  hMul m t := ⟨t.coeff, m * t.monom⟩

instance [Div R] : Div (Term R α) where
  div t₁ t₂ := ⟨t₁.coeff / t₂.coeff, t₁.monom / t₂.monom⟩

instance [Neg R] : Neg (Term R α) where
  neg t := ⟨-t.coeff, t.monom⟩

def ofVar [OfNat R <| nat_lit 1] (a : α) : Term R α := ⟨1, Monomial.ofVar a⟩

instance [Dvd R] : Dvd (Term R α) where
  dvd t₁ t₂ := t₁.coeff ∣ t₂.coeff && t₁.monom ∣ t₂.monom

instance [Inhabited R] : Inhabited (Term R α) := ⟨⟨default, default⟩⟩

instance [BEq R] : BEq (Term R α) where
  beq t₁ t₂ := t₁.coeff == t₂.coeff && t₁.monom == t₂.monom

instance [OfNat R <| nat_lit 1] : OfNat (Term R α) <| nat_lit 1 :=
  ⟨1, 1⟩

def ofMonomial [OfNat R <| nat_lit 1] (m : Monomial α) : Term R α :=
  ⟨1, m⟩

end Term
