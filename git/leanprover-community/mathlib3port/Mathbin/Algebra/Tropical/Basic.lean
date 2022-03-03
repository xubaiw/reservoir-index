/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Algebra.GroupPower.Order
import Mathbin.Algebra.SmulWithZero

/-!

# Tropical algebraic structures

This file defines algebraic structures of the (min-)tropical numbers, up to the tropical semiring.
Some basic lemmas about conversion from the base type `R` to `tropical R` are provided, as
well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `tropical R`: The type synonym of the tropical interpretation of `R`.
    If `[linear_order R]`, then addition on `R` is via `min`.
* `semiring (tropical R)`: A `linear_ordered_add_comm_monoid_with_top R`
    induces a `semiring (tropical R)`. If one solely has `[linear_ordered_add_comm_monoid R]`,
    then the "tropicalization of `R`" would be `tropical (with_top R)`.

## Implementation notes

The tropical structure relies on `has_top` and `min`. For the max-tropical numbers, use
`order_dual R`.

Inspiration was drawn from the implementation of `additive`/`multiplicative`/`opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `semiring (tropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/


universe u v

variable (R : Type u)

/-- The tropicalization of a type `R`. -/
def Tropical : Type u :=
  R

variable {R}

namespace Tropical

/-- Reinterpret `x : R` as an element of `tropical R`.
See `tropical.trop_equiv` for the equivalence.
-/
@[pp_nodot]
def trop : R → Tropical R :=
  id

/-- Reinterpret `x : tropical R` as an element of `R`.
See `tropical.trop_equiv` for the equivalence. -/
@[pp_nodot]
def untrop : Tropical R → R :=
  id

theorem trop_injective : Function.Injective (trop : R → Tropical R) := fun _ _ => id

theorem untrop_injective : Function.Injective (untrop : Tropical R → R) := fun _ _ => id

@[simp]
theorem trop_inj_iff (x y : R) : trop x = trop y ↔ x = y :=
  Iff.rfl

@[simp]
theorem untrop_inj_iff (x y : Tropical R) : untrop x = untrop y ↔ x = y :=
  Iff.rfl

@[simp]
theorem trop_untrop (x : Tropical R) : trop (untrop x) = x :=
  rfl

@[simp]
theorem untrop_trop (x : R) : untrop (trop x) = x :=
  rfl

theorem left_inverse_trop : Function.LeftInverse (trop : R → Tropical R) untrop :=
  trop_untrop

theorem right_inverse_trop : Function.RightInverse (trop : R → Tropical R) untrop :=
  trop_untrop

/-- Reinterpret `x : R` as an element of `tropical R`.
See `tropical.trop_order_iso` for the order-preserving equivalence. -/
def tropEquiv : R ≃ Tropical R where
  toFun := trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop

@[simp]
theorem trop_equiv_coe_fn : (tropEquiv : R → Tropical R) = trop :=
  rfl

@[simp]
theorem trop_equiv_symm_coe_fn : (tropEquiv.symm : Tropical R → R) = untrop :=
  rfl

theorem trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y :=
  tropEquiv.apply_eq_iff_eq_symm_apply

theorem untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y :=
  tropEquiv.symm.apply_eq_iff_eq_symm_apply

theorem injective_trop : Function.Injective (trop : R → Tropical R) :=
  tropEquiv.Injective

theorem injective_untrop : Function.Injective (untrop : Tropical R → R) :=
  tropEquiv.symm.Injective

theorem surjective_trop : Function.Surjective (trop : R → Tropical R) :=
  tropEquiv.Surjective

theorem surjective_untrop : Function.Surjective (untrop : Tropical R → R) :=
  tropEquiv.symm.Surjective

instance [Inhabited R] : Inhabited (Tropical R) :=
  ⟨trop default⟩

/-- Recursing on a `x' : tropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `tropical R` via `trop x`. -/
@[simp]
def tropRec {F : ∀ X : Tropical R, Sort v} (h : ∀ X, F (trop X)) : ∀ X, F X := fun X => h (untrop X)

instance [DecidableEq R] : DecidableEq (Tropical R) := fun x y => decidableOfIff _ injective_untrop.eq_iff

section Order

instance [LE R] : LE (Tropical R) where
  le := fun x y => untrop x ≤ untrop y

@[simp]
theorem untrop_le_iff [LE R] {x y : Tropical R} : untrop x ≤ untrop y ↔ x ≤ y :=
  Iff.rfl

instance decidableLe [LE R] [DecidableRel ((· ≤ ·) : R → R → Prop)] :
    DecidableRel ((· ≤ ·) : Tropical R → Tropical R → Prop) := fun x y => ‹DecidableRel (· ≤ ·)› (untrop x) (untrop y)

instance [LT R] : LT (Tropical R) where
  lt := fun x y => untrop x < untrop y

@[simp]
theorem untrop_lt_iff [LT R] {x y : Tropical R} : untrop x < untrop y ↔ x < y :=
  Iff.rfl

instance decidableLt [LT R] [DecidableRel ((· < ·) : R → R → Prop)] :
    DecidableRel ((· < ·) : Tropical R → Tropical R → Prop) := fun x y => ‹DecidableRel (· < ·)› (untrop x) (untrop y)

instance [Preorderₓ R] : Preorderₓ (Tropical R) :=
  { Tropical.hasLe, Tropical.hasLt with le_refl := fun _ => le_rfl, le_trans := fun _ _ _ h h' => le_transₓ h h',
    lt_iff_le_not_le := fun _ _ => lt_iff_le_not_leₓ }

/-- Reinterpret `x : R` as an element of `tropical R`, preserving the order. -/
def tropOrderIso [Preorderₓ R] : R ≃o Tropical R :=
  { tropEquiv with map_rel_iff' := fun _ _ => untrop_le_iff }

@[simp]
theorem trop_order_iso_coe_fn [Preorderₓ R] : (tropOrderIso : R → Tropical R) = trop :=
  rfl

@[simp]
theorem trop_order_iso_symm_coe_fn [Preorderₓ R] : (tropOrderIso.symm : Tropical R → R) = untrop :=
  rfl

theorem trop_monotone [Preorderₓ R] : Monotone (trop : R → Tropical R) := fun _ _ => id

theorem untrop_monotone [Preorderₓ R] : Monotone (untrop : Tropical R → R) := fun _ _ => id

instance [PartialOrderₓ R] : PartialOrderₓ (Tropical R) :=
  { Tropical.preorder with le_antisymm := fun _ _ h h' => untrop_injective (le_antisymmₓ h h') }

instance [HasTop R] : Zero (Tropical R) :=
  ⟨trop ⊤⟩

instance [HasTop R] : HasTop (Tropical R) :=
  ⟨0⟩

@[simp]
theorem untrop_zero [HasTop R] : untrop (0 : Tropical R) = ⊤ :=
  rfl

@[simp]
theorem trop_top [HasTop R] : trop (⊤ : R) = 0 :=
  rfl

@[simp]
theorem trop_coe_ne_zero (x : R) : trop (x : WithTop R) ≠ 0 :=
  fun.

@[simp]
theorem zero_ne_trop_coe (x : R) : (0 : Tropical (WithTop R)) ≠ trop x :=
  fun.

@[simp]
theorem le_zero [LE R] [OrderTop R] (x : Tropical R) : x ≤ 0 :=
  le_top

instance [LE R] [OrderTop R] : OrderTop (Tropical R) :=
  { Tropical.hasTop with le_top := fun _ => le_top }

variable [LinearOrderₓ R]

/-- Tropical addition is the minimum of two underlying elements of `R`. -/
instance : Add (Tropical R) :=
  ⟨fun x y => trop (min (untrop x) (untrop y))⟩

instance : AddCommSemigroupₓ (Tropical R) where
  add := (· + ·)
  add_assoc := fun _ _ _ => untrop_injective (min_assocₓ _ _ _)
  add_comm := fun _ _ => untrop_injective (min_commₓ _ _)

@[simp]
theorem untrop_add (x y : Tropical R) : untrop (x + y) = min (untrop x) (untrop y) :=
  rfl

@[simp]
theorem trop_min (x y : R) : trop (min x y) = trop x + trop y :=
  rfl

@[simp]
theorem trop_inf (x y : R) : trop (x⊓y) = trop x + trop y :=
  rfl

theorem trop_add_def (x y : Tropical R) : x + y = trop (min (untrop x) (untrop y)) :=
  rfl

instance : LinearOrderₓ (Tropical R) :=
  { Tropical.partialOrder with le_total := fun a b => le_totalₓ (untrop a) (untrop b),
    decidableLe := Tropical.decidableLe, decidableLt := Tropical.decidableLt, DecidableEq := Tropical.decidableEq,
    max := fun a b => trop (max (untrop a) (untrop b)),
    max_def := by
      ext x y
      rw [maxDefault, max_def, apply_ite trop, trop_untrop, trop_untrop, if_congr untrop_le_iff rfl rfl],
    min := (· + ·),
    min_def := by
      ext x y
      rw [trop_add_def, minDefault, min_def, apply_ite trop, trop_untrop, trop_untrop, if_congr untrop_le_iff rfl rfl] }

@[simp]
theorem untrop_sup (x y : Tropical R) : untrop (x⊔y) = untrop x⊔untrop y :=
  rfl

@[simp]
theorem untrop_max (x y : Tropical R) : untrop (max x y) = max (untrop x) (untrop y) :=
  rfl

@[simp]
theorem min_eq_add : (min : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl

@[simp]
theorem inf_eq_add : ((·⊓·) : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl

theorem trop_max_def (x y : Tropical R) : max x y = trop (max (untrop x) (untrop y)) :=
  rfl

theorem trop_sup_def (x y : Tropical R) : x⊔y = trop (untrop x⊔untrop y) :=
  rfl

@[simp]
theorem add_eq_left ⦃x y : Tropical R⦄ (h : x ≤ y) : x + y = x :=
  untrop_injective
    (by
      simpa using h)

@[simp]
theorem add_eq_right ⦃x y : Tropical R⦄ (h : y ≤ x) : x + y = y :=
  untrop_injective
    (by
      simpa using h)

theorem add_eq_left_iff {x y : Tropical R} : x + y = x ↔ x ≤ y := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_left_iff]

theorem add_eq_right_iff {x y : Tropical R} : x + y = y ↔ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_right_iff]

@[simp]
theorem add_self (x : Tropical R) : x + x = x :=
  untrop_injective (min_eq_rightₓ le_rfl)

@[simp]
theorem bit0 (x : Tropical R) : bit0 x = x :=
  add_self x

theorem add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z ∧ x ≤ y ∨ y = z ∧ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop]
  simp [min_eq_iff]

@[simp]
theorem add_eq_zero_iff {a b : Tropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymmₓ (le_zero _) h⟩
      
    · exact ⟨le_antisymmₓ (le_zero _) h, rfl⟩
      
    
  · rintro ⟨rfl, rfl⟩
    simp
    

instance [OrderTop R] : AddCommMonoidₓ (Tropical R) :=
  { Tropical.hasZero, Tropical.addCommSemigroup with zero_add := fun _ => untrop_injective (min_top_left _),
    add_zero := fun _ => untrop_injective (min_top_right _) }

end Order

section Monoidₓ

/-- Tropical multiplication is the addition in the underlying `R`. -/
instance [Add R] : Mul (Tropical R) :=
  ⟨fun x y => trop (untrop x + untrop y)⟩

@[simp]
theorem trop_add [Add R] (x y : R) : trop (x + y) = trop x * trop y :=
  rfl

@[simp]
theorem untrop_mul [Add R] (x y : Tropical R) : untrop (x * y) = untrop x + untrop y :=
  rfl

theorem trop_mul_def [Add R] (x y : Tropical R) : x * y = trop (untrop x + untrop y) :=
  rfl

instance [Zero R] : One (Tropical R) :=
  ⟨trop 0⟩

@[simp]
theorem trop_zero [Zero R] : trop (0 : R) = 1 :=
  rfl

@[simp]
theorem untrop_one [Zero R] : untrop (1 : Tropical R) = 0 :=
  rfl

instance [Zero R] : Nontrivial (Tropical (WithTop R)) :=
  ⟨⟨0, 1, trop_injective.Ne WithTop.top_ne_coe⟩⟩

instance [Neg R] : Inv (Tropical R) :=
  ⟨fun x => trop (-untrop x)⟩

@[simp]
theorem untrop_inv [Neg R] (x : Tropical R) : untrop x⁻¹ = -untrop x :=
  rfl

instance [Sub R] : Div (Tropical R) :=
  ⟨fun x y => trop (untrop x - untrop y)⟩

@[simp]
theorem untrop_div [Sub R] (x y : Tropical R) : untrop (x / y) = untrop x - untrop y :=
  rfl

instance [AddSemigroupₓ R] : Semigroupₓ (Tropical R) where
  mul := (· * ·)
  mul_assoc := fun _ _ _ => untrop_injective (add_assocₓ _ _ _)

instance [AddCommSemigroupₓ R] : CommSemigroupₓ (Tropical R) :=
  { Tropical.semigroup with mul_comm := fun _ _ => untrop_injective (add_commₓ _ _) }

instance {α : Type _} [HasScalar α R] : Pow (Tropical R) α where
  pow := fun x n => trop <| n • untrop x

@[simp]
theorem untrop_pow {α : Type _} [HasScalar α R] (x : Tropical R) (n : α) : untrop (x ^ n) = n • untrop x :=
  rfl

@[simp]
theorem trop_smul {α : Type _} [HasScalar α R] (x : R) (n : α) : trop (n • x) = trop x ^ n :=
  rfl

instance [AddZeroClass R] : MulOneClassₓ (Tropical R) where
  one := 1
  mul := (· * ·)
  one_mul := fun _ => untrop_injective <| zero_addₓ _
  mul_one := fun _ => untrop_injective <| add_zeroₓ _

instance [AddMonoidₓ R] : Monoidₓ (Tropical R) :=
  { Tropical.mulOneClass, Tropical.semigroup with npow := fun n x => x ^ n,
    npow_zero' := fun _ => untrop_injective <| zero_smul _ _,
    npow_succ' := fun _ _ => untrop_injective <| succ_nsmul _ _ }

@[simp]
theorem trop_nsmul [AddMonoidₓ R] (x : R) (n : ℕ) : trop (n • x) = trop x ^ n :=
  rfl

instance [AddCommMonoidₓ R] : CommMonoidₓ (Tropical R) :=
  { Tropical.monoid, Tropical.commSemigroup with }

instance [AddGroupₓ R] : Groupₓ (Tropical R) :=
  { Tropical.monoid with inv := Inv.inv, mul_left_inv := fun _ => untrop_injective <| add_left_negₓ _,
    zpow := fun n x => trop <| n • untrop x, zpow_zero' := fun _ => untrop_injective <| zero_zsmul _,
    zpow_succ' := fun _ _ => untrop_injective <| AddGroupₓ.zsmul_succ' _ _,
    zpow_neg' := fun _ _ => untrop_injective <| AddGroupₓ.zsmul_neg' _ _ }

instance [AddCommGroupₓ R] : CommGroupₓ (Tropical R) :=
  { Tropical.group with mul_comm := fun _ _ => untrop_injective (add_commₓ _ _) }

@[simp]
theorem untrop_zpow [AddGroupₓ R] (x : Tropical R) (n : ℤ) : untrop (x ^ n) = n • untrop x :=
  rfl

@[simp]
theorem trop_zsmul [AddGroupₓ R] (x : R) (n : ℤ) : trop (n • x) = trop x ^ n :=
  rfl

end Monoidₓ

section Distribₓ

instance covariant_mul [LE R] [Add R] [CovariantClass R R (· + ·) (· ≤ ·)] :
    CovariantClass (Tropical R) (Tropical R) (· * ·) (· ≤ ·) :=
  ⟨fun x y z h => add_le_add_left h _⟩

instance covariant_swap_mul [LE R] [Add R] [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] :
    CovariantClass (Tropical R) (Tropical R) (Function.swap (· * ·)) (· ≤ ·) :=
  ⟨fun x y z h => add_le_add_right h _⟩

instance covariant_add [LinearOrderₓ R] : CovariantClass (Tropical R) (Tropical R) (· + ·) (· ≤ ·) :=
  ⟨fun x y z h => by
    cases' le_totalₓ x y with hx hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
      
    · rw [add_eq_right hy]
      cases' le_totalₓ x z with hx hx
      · rwa [add_eq_left hx]
        
      · rwa [add_eq_right hx]
        
      ⟩

instance covariant_mul_lt [LT R] [Add R] [CovariantClass R R (· + ·) (· < ·)] :
    CovariantClass (Tropical R) (Tropical R) (· * ·) (· < ·) :=
  ⟨fun x y z h => add_lt_add_left h _⟩

instance covariant_swap_mul_lt [Preorderₓ R] [Add R] [CovariantClass R R (Function.swap (· + ·)) (· < ·)] :
    CovariantClass (Tropical R) (Tropical R) (Function.swap (· * ·)) (· < ·) :=
  ⟨fun x y z h => add_lt_add_right h _⟩

instance [LinearOrderₓ R] [Add R] [CovariantClass R R (· + ·) (· ≤ ·)]
    [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] : Distribₓ (Tropical R) where
  mul := (· * ·)
  add := (· + ·)
  left_distrib := fun _ _ _ => untrop_injective (min_add_add_left _ _ _).symm
  right_distrib := fun _ _ _ => untrop_injective (min_add_add_right _ _ _).symm

@[simp]
theorem add_pow [LinearOrderₓ R] [AddMonoidₓ R] [CovariantClass R R (· + ·) (· ≤ ·)]
    [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] (x y : Tropical R) (n : ℕ) : (x + y) ^ n = x ^ n + y ^ n := by
  cases' le_totalₓ x y with h h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_of_le_left' h _)]
    
  · rw [add_eq_right h, add_eq_right (pow_le_pow_of_le_left' h _)]
    

end Distribₓ

section Semiringₓ

variable [LinearOrderedAddCommMonoidWithTop R]

instance : CommSemiringₓ (Tropical R) :=
  { Tropical.hasZero, Tropical.distrib, Tropical.addCommMonoid, Tropical.commMonoid with
    zero_mul := fun _ => untrop_injective (top_add _), mul_zero := fun _ => untrop_injective (add_top _) }

@[simp]
theorem succ_nsmul {R} [LinearOrderₓ R] [OrderTop R] (x : Tropical R) (n : ℕ) : (n + 1) • x = x := by
  induction' n with n IH
  · simp
    
  · rw [add_nsmul, IH, one_nsmul, add_self]
    

-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma add_eq_zero_iff {a b : tropical R} :
--   a + b = 1 ↔ a = 1 ∨ b = 1 := sorry
@[simp]
theorem mul_eq_zero_iff {R : Type _} [LinearOrderedAddCommMonoid R] {a b : Tropical (WithTop R)} :
    a * b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [← untrop_inj_iff, WithTop.add_eq_top]

instance {R : Type _} [LinearOrderedAddCommMonoid R] : NoZeroDivisors (Tropical (WithTop R)) :=
  ⟨fun _ _ => mul_eq_zero_iff.mp⟩

end Semiringₓ

end Tropical

