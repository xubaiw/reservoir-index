import Iva.Data.HashMap
import Iva.Algebra.Dvd

open Std

structure Monomial (α : Type u) [BEq α] [Hashable α] :=
(exponents : HashMap α Nat)

namespace Monomial

variable {α : Type u} [BEq α] [Hashable α]

def degree (m : Monomial α) : Nat :=
  m.exponents.fold (init := 0) λ n _ m => n + m

def exponent (m : Monomial α) (a : α) : Nat :=
  m.exponents.findD a 0

def variables (m : Monomial α) : HashSet α :=
  m.exponents.fold (init := HashSet.empty) λ s a m => if m == 0 then s else s.insert a

instance : Mul (Monomial α) where
  mul m₁ m₂ := 
    let v := m₁.variables.union m₂.variables
    ⟨v.fold (init := HashMap.empty) λ m a => m.insert a <| m₁.exponent a + m₂.exponent a⟩

instance : Div (Monomial α) where
  div m₁ m₂ :=
    ⟨m₁.exponents.fold (init := HashMap.empty) λ m a k => m.insert a <| k - m₂.exponent a⟩ 

instance : BEq (Monomial α) where
  beq m₁ m₂ := m₁.exponents == m₂.exponents

def divides (m₁ m₂ : Monomial α) : Bool :=
  m₁.exponents.fold (init := true) λ b a n => b && n ≤ m₂.exponent a

instance : Dvd (Monomial α) := ⟨divides⟩

def ofVar (a : α) : Monomial α := ⟨HashMap.ofList [(a, 1)]⟩

instance : Inhabited (Monomial α) := ⟨⟨HashMap.empty⟩⟩

instance : OfNat (Monomial α) <| nat_lit 1 := ⟨⟨HashMap.empty⟩⟩

def lcm (m₁ m₂ : Monomial α) : Monomial α :=
  let vars := m₁.exponents.keys.union m₂.exponents.keys
  ⟨vars.fold (init := HashMap.empty) λ m a => m.insert a 
    <| max (m₁.exponent a) (m₂.exponent a)⟩

end Monomial
