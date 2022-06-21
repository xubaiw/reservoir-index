import Polylean.GardamGroup
import Polylean.GroupRing


/-
The proof of the theorem `𝔽₂[P]` has non-trivial units. Together with the main result of `TorsionFree` -- that `P` is torsion-free, this completes the formal proof of Gardam's theorem that Kaplansky's Unit Conjecture is false.
-/


section preliminaries

/-- definition of a unit -/
def unit {R : Type _} [Ring R] (u : R) := ∃ v : R, v * u = (1 : R)

/-- definition of being trivial, i.e., of the form `a⬝g` for `g` a group element and `a ≠ 0`-/
def trivial_element {R G : Type _} [CommRing R] [DecidableEq R] [Group G] [DecidableEq G] (x : FreeModule R G) : Prop :=
  ∃ g : G, ¬(FreeModule.coordinates g x = 0) ∧ (∀ h : G, ¬(FreeModule.coordinates h x = 0) → h = g)

abbrev R := Fin 2

abbrev P := P.P

abbrev RP := FreeModule R P

instance ringElem: Coe P (RP) where
    coe g :=  ⟦[(1, g)]⟧

end preliminaries

namespace Gardam
section constants

abbrev x : P := (P.x, P.e)
abbrev y : P := (P.y, P.e)
abbrev z : P := (P.z, P.e)
abbrev a : P := ((0, 0, 0), P.a)
abbrev b : P := ((0, 0, 0), P.b)
abbrev one : RP := 1


/-! The components of the non-trivial unit `α` -/
def p : RP := one +  x +  y +  x*y +  z⁻¹ + x*z⁻¹ + y*z⁻¹ + x*y*z⁻¹
def q : RP := (x⁻¹*y⁻¹ : RP) + x + y⁻¹*z + z
def r: RP := one + x + y⁻¹*z + x*y*z
def s : RP  := one + x*z⁻¹ + x⁻¹*z⁻¹ + y*z⁻¹ + y⁻¹*z⁻¹

/-- the non-trivial unit `α` -/
def α := p + (q * a) + (r * b) + (s * a * b)
 
/-! The components of the inverse `α'` of the non-trivial unit `α` -/
def p' : RP := x⁻¹ * (a⁻¹  * p * a)
def q' : RP := -(x⁻¹ * q)
def r' : RP := -(y⁻¹ * r)
def s' : RP := z⁻¹ * (a⁻¹ * s * a)

end constants


section verification

/-- the inverse `α'` of the non-trivial unit `α` -/
def α' := p' + (q' * a) + (r' * b) + (s' * a * b)


/-- `α` is a unit -/
theorem α_is_unit : unit α := ⟨α', by native_decide⟩

/-- `α` is  non-trivial -/
theorem α_non_trivial : ¬ (trivial_element α) := by
    intro contra
    let ⟨g, p⟩ := contra
    let eqg := p.right
    have eq₁ : -z = g := by 
      apply eqg
      native_decide
    have eq₂ : x * y = g := by
      apply eqg
      native_decide
    rw [← eq₂] at eq₁
    contradiction

/-- the existence of a non-trivial unit in `𝔽₂[P]` -/
theorem Gardam : ∃ g : RP, unit g ∧ ¬ (trivial_element g) := 
  ⟨α, And.intro α_is_unit α_non_trivial⟩

end verification

end Gardam
