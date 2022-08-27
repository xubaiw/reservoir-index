/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
-/
import Mathbin.Order.Heyting.Basic

/-!
# (Generalized) Boolean algebras

A Boolean algebra is a bounded distributive lattice with a complement operator. Boolean algebras
generalize the (classical) logic of propositions and the lattice of subsets of a set.

Generalized Boolean algebras may be less familiar, but they are essentially Boolean algebras which
do not necessarily have a top element (`⊤`) (and hence not all elements may have complements). One
example in mathlib is `finset α`, the type of all finite subsets of an arbitrary
(not-necessarily-finite) type `α`.

`generalized_boolean_algebra α` is defined to be a distributive lattice with bottom (`⊥`) admitting
a *relative* complement operator, written using "set difference" notation as `x \ y` (`sdiff x y`).
For convenience, the `boolean_algebra` type class is defined to extend `generalized_boolean_algebra`
so that it is also bundled with a `\` operator.

(A terminological point: `x \ y` is the complement of `y` relative to the interval `[⊥, x]`. We do
not yet have relative complements for arbitrary intervals, as we do not even have lattice
intervals.)

## Main declarations

* `generalized_boolean_algebra`: a type class for generalized Boolean algebras
* `boolean_algebra`: a type class for Boolean algebras.
* `Prop.boolean_algebra`: the Boolean algebra instance on `Prop`

## Implementation notes

The `sup_inf_sdiff` and `inf_inf_sdiff` axioms for the relative complement operator in
`generalized_boolean_algebra` are taken from
[Wikipedia](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations).

[Stone's paper introducing generalized Boolean algebras][Stone1935] does not define a relative
complement operator `a \ b` for all `a`, `b`. Instead, the postulates there amount to an assumption
that for all `a, b : α` where `a ≤ b`, the equations `x ⊔ a = b` and `x ⊓ a = ⊥` have a solution
`x`. `disjoint.sdiff_unique` proves that this `x` is in fact `b \ a`.

## References

* <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>
* [*Postulates for Boolean Algebras and Generalized Boolean Algebras*, M.H. Stone][Stone1935]
* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl
-/


open Function OrderDual

universe u v

variable {α : Type u} {β : Type _} {w x y z : α}

/-!
### Generalized Boolean algebras

Some of the lemmas in this section are from:

* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]
* <https://ncatlab.org/nlab/show/relative+complement>
* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

-/


/-- A generalized Boolean algebra is a distributive lattice with `⊥` and a relative complement
operation `\` (called `sdiff`, after "set difference") satisfying `(a ⊓ b) ⊔ (a \ b) = a` and
`(a ⊓ b) ⊓ (a \ b) = ⊥`, i.e. `a \ b` is the complement of `b` in `a`.

This is a generalization of Boolean algebras which applies to `finset α` for arbitrary
(not-necessarily-`fintype`) `α`. -/
class GeneralizedBooleanAlgebra (α : Type u) extends DistribLattice α, Sdiff α, HasBot α where
  sup_inf_sdiff : ∀ a b : α, a⊓b⊔a \ b = a
  inf_inf_sdiff : ∀ a b : α, a⊓b⊓a \ b = ⊥

-- We might want a `is_compl_of` predicate (for relative complements) generalizing `is_compl`,
-- however we'd need another type class for lattices with bot, and all the API for that.
section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

@[simp]
theorem sup_inf_sdiff (x y : α) : x⊓y⊔x \ y = x :=
  GeneralizedBooleanAlgebra.sup_inf_sdiff _ _

@[simp]
theorem inf_inf_sdiff (x y : α) : x⊓y⊓x \ y = ⊥ :=
  GeneralizedBooleanAlgebra.inf_inf_sdiff _ _

@[simp]
theorem sup_sdiff_inf (x y : α) : x \ y⊔x⊓y = x := by
  rw [sup_comm, sup_inf_sdiff]

@[simp]
theorem inf_sdiff_inf (x y : α) : x \ y⊓(x⊓y) = ⊥ := by
  rw [inf_comm, inf_inf_sdiff]

-- see Note [lower instance priority]
instance (priority := 100) GeneralizedBooleanAlgebra.toOrderBot : OrderBot α :=
  { GeneralizedBooleanAlgebra.toHasBot α with
    bot_le := fun a => by
      rw [← inf_inf_sdiff a a, inf_assoc]
      exact inf_le_left }

theorem disjoint_inf_sdiff : Disjoint (x⊓y) (x \ y) :=
  (inf_inf_sdiff x y).le

-- TODO: in distributive lattices, relative complements are unique when they exist
theorem sdiff_unique (s : x⊓y⊔z = x) (i : x⊓y⊓z = ⊥) : x \ y = z := by
  conv_rhs at s => rw [← sup_inf_sdiff x y, sup_comm]
  rw [sup_comm] at s
  conv_rhs at i => rw [← inf_inf_sdiff x y, inf_comm]
  rw [inf_comm] at i
  exact (eq_of_inf_eq_sup_eq i s).symm

theorem sdiff_le' : x \ y ≤ x :=
  calc
    x \ y ≤ x⊓y⊔x \ y := le_sup_right
    _ = x := sup_inf_sdiff x y
    

theorem inf_sdiff_right : x⊓x \ y = x \ y :=
  inf_of_le_right (@sdiff_le' _ x y _)

theorem inf_sdiff_left : x \ y⊓x = x \ y := by
  rw [inf_comm, inf_sdiff_right]

@[simp]
theorem sup_sdiff_self_right : x⊔y \ x = x⊔y :=
  calc
    x⊔y \ x = x⊔x⊓y⊔y \ x := by
      rw [sup_inf_self]
    _ = x⊔(y⊓x⊔y \ x) := by
      ac_rfl
    _ = x⊔y := by
      rw [sup_inf_sdiff]
    

@[simp]
theorem sup_sdiff_self_left : y \ x⊔x = y⊔x := by
  rw [sup_comm, sup_sdiff_self_right, sup_comm]

theorem sup_sdiff_symm : x⊔y \ x = y⊔x \ y := by
  rw [sup_sdiff_self_right, sup_sdiff_self_right, sup_comm]

theorem sup_sdiff_cancel_right (h : x ≤ y) : x⊔y \ x = y := by
  conv_rhs => rw [← sup_inf_sdiff y x, inf_eq_right.2 h]

theorem sdiff_sup_cancel (h : y ≤ x) : x \ y⊔y = x := by
  rw [sup_comm, sup_sdiff_cancel_right h]

theorem sup_le_of_le_sdiff_left (h : y ≤ z \ x) (hxz : x ≤ z) : x⊔y ≤ z :=
  (sup_le_sup_left h x).trans (sup_sdiff_cancel_right hxz).le

theorem sup_le_of_le_sdiff_right (h : x ≤ z \ y) (hyz : y ≤ z) : x⊔y ≤ z :=
  (sup_le_sup_right h y).trans (sdiff_sup_cancel hyz).le

@[simp]
theorem sup_sdiff_left : x⊔x \ y = x :=
  sup_eq_left.2 sdiff_le'

theorem sup_sdiff_right : x \ y⊔x = x :=
  sup_eq_right.2 sdiff_le'

@[simp]
theorem sdiff_inf_sdiff : x \ y⊓y \ x = ⊥ :=
  Eq.symm <|
    calc
      ⊥ = x⊓y⊓x \ y := by
        rw [inf_inf_sdiff]
      _ = x⊓(y⊓x⊔y \ x)⊓x \ y := by
        rw [sup_inf_sdiff]
      _ = (x⊓(y⊓x)⊔x⊓y \ x)⊓x \ y := by
        rw [inf_sup_left]
      _ = (y⊓(x⊓x)⊔x⊓y \ x)⊓x \ y := by
        ac_rfl
      _ = (y⊓x⊔x⊓y \ x)⊓x \ y := by
        rw [inf_idem]
      _ = x⊓y⊓x \ y⊔x⊓y \ x⊓x \ y := by
        rw [inf_sup_right, @inf_comm _ _ x y]
      _ = x⊓y \ x⊓x \ y := by
        rw [inf_inf_sdiff, bot_sup_eq]
      _ = x⊓x \ y⊓y \ x := by
        ac_rfl
      _ = x \ y⊓y \ x := by
        rw [inf_sdiff_right]
      

theorem disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x) :=
  sdiff_inf_sdiff.le

@[simp]
theorem inf_sdiff_self_right : x⊓y \ x = ⊥ :=
  calc
    x⊓y \ x = (x⊓y⊔x \ y)⊓y \ x := by
      rw [sup_inf_sdiff]
    _ = x⊓y⊓y \ x⊔x \ y⊓y \ x := by
      rw [inf_sup_right]
    _ = ⊥ := by
      rw [@inf_comm _ _ x y, inf_inf_sdiff, sdiff_inf_sdiff, bot_sup_eq]
    

@[simp]
theorem inf_sdiff_self_left : y \ x⊓x = ⊥ := by
  rw [inf_comm, inf_sdiff_self_right]

-- see Note [lower instance priority]
instance (priority := 100) GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra : GeneralizedCoheytingAlgebra α :=
  { ‹GeneralizedBooleanAlgebra α›, GeneralizedBooleanAlgebra.toOrderBot with sdiff := (· \ ·),
    sdiff_le_iff := fun y x z =>
      ⟨fun h =>
        le_of_inf_le_sup_le
          (le_of_eqₓ
            (calc
              y⊓y \ x = y \ x := inf_sdiff_right
              _ = x⊓y \ x⊔z⊓y \ x := by
                rw [inf_eq_right.2 h, inf_sdiff_self_right, bot_sup_eq]
              _ = (x⊔z)⊓y \ x := inf_sup_right.symm
              ))
          (calc
            y⊔y \ x = y := sup_sdiff_left
            _ ≤ y⊔(x⊔z) := le_sup_left
            _ = y \ x⊔x⊔z := by
              rw [← sup_assoc, ← @sup_sdiff_self_left _ x y]
            _ = x⊔z⊔y \ x := by
              ac_rfl
            ),
        fun h =>
        le_of_inf_le_sup_le
          (calc
            y \ x⊓x = ⊥ := inf_sdiff_self_left
            _ ≤ z⊓x := bot_le
            )
          (calc
            y \ x⊔x = y⊔x := sup_sdiff_self_left
            _ ≤ x⊔z⊔x := sup_le_sup_right h x
            _ ≤ z⊔x := by
              rw [sup_assoc, sup_comm, sup_assoc, sup_idem]
            )⟩ }

theorem disjoint_sdiff_self_left : Disjoint (y \ x) x :=
  inf_sdiff_self_left.le

theorem disjoint_sdiff_self_right : Disjoint x (y \ x) :=
  inf_sdiff_self_right.le

/- TODO: we could make an alternative constructor for `generalized_boolean_algebra` using
`disjoint x (y \ x)` and `x ⊔ (y \ x) = y` as axioms. -/
theorem Disjoint.sdiff_eq_of_sup_eq (hi : Disjoint x z) (hs : x⊔z = y) : y \ x = z :=
  have h : y⊓x = x := inf_eq_right.2 <| le_sup_left.trans hs.le
  sdiff_unique
    (by
      rw [h, hs])
    (by
      rw [h, hi.eq_bot])

theorem Disjoint.sup_sdiff_cancel_left (h : Disjoint x y) : (x⊔y) \ x = y :=
  h.sdiff_eq_of_sup_eq rfl

theorem Disjoint.sup_sdiff_cancel_right (h : Disjoint x y) : (x⊔y) \ y = x :=
  h.symm.sdiff_eq_of_sup_eq sup_comm

protected theorem Disjoint.sdiff_unique (hd : Disjoint x z) (hz : z ≤ y) (hs : y ≤ x⊔z) : y \ x = z :=
  sdiff_unique
    (by
      rw [← inf_eq_right] at hs
      rwa [sup_inf_right, inf_sup_right, @sup_comm _ _ x, inf_sup_self, inf_comm, @sup_comm _ _ z, hs, sup_eq_left])
    (by
      rw [inf_assoc, hd.eq_bot, inf_bot_eq])

-- cf. `is_compl.disjoint_left_iff` and `is_compl.disjoint_right_iff`
theorem disjoint_sdiff_iff_le (hz : z ≤ y) (hx : x ≤ y) : Disjoint z (y \ x) ↔ z ≤ x :=
  ⟨fun H =>
    le_of_inf_le_sup_le (le_transₓ H bot_le)
      (by
        rw [sup_sdiff_cancel_right hx]
        refine' le_transₓ (sup_le_sup_left sdiff_le z) _
        rw [sup_eq_right.2 hz]),
    fun H => disjoint_sdiff_self_right.mono_left H⟩

-- cf. `is_compl.le_left_iff` and `is_compl.le_right_iff`
theorem le_iff_disjoint_sdiff (hz : z ≤ y) (hx : x ≤ y) : z ≤ x ↔ Disjoint z (y \ x) :=
  (disjoint_sdiff_iff_le hz hx).symm

-- cf. `is_compl.inf_left_eq_bot_iff` and `is_compl.inf_right_eq_bot_iff`
theorem inf_sdiff_eq_bot_iff (hz : z ≤ y) (hx : x ≤ y) : z⊓y \ x = ⊥ ↔ z ≤ x := by
  rw [← disjoint_iff]
  exact disjoint_sdiff_iff_le hz hx

-- cf. `is_compl.left_le_iff` and `is_compl.right_le_iff`
theorem le_iff_eq_sup_sdiff (hz : z ≤ y) (hx : x ≤ y) : x ≤ z ↔ y = z⊔y \ x :=
  ⟨fun H => by
    apply le_antisymmₓ
    · conv_lhs => rw [← sup_inf_sdiff y x]
      apply sup_le_sup_right
      rwa [inf_eq_right.2 hx]
      
    · apply le_transₓ
      · apply sup_le_sup_right hz
        
      · rw [sup_sdiff_left]
        
      ,
    fun H => by
    conv_lhs at H => rw [← sup_sdiff_cancel_right hx]
    refine' le_of_inf_le_sup_le _ H.le
    rw [inf_sdiff_self_right]
    exact bot_le⟩

theorem sup_sdiff_eq_sup (h : z ≤ x) : x⊔y \ z = x⊔y :=
  sup_congr_left (sdiff_le.trans le_sup_right) <| le_sup_sdiff.trans <| sup_le_sup_right h _

-- cf. `set.union_diff_cancel'`
theorem sup_sdiff_cancel' (hx : x ≤ z) (hz : z ≤ y) : z⊔y \ x = y :=
  ((le_iff_eq_sup_sdiff hz (hx.trans hz)).1 hx).symm

-- cf. `is_compl.sup_inf`
theorem sdiff_sup : y \ (x⊔z) = y \ x⊓y \ z :=
  sdiff_unique
    (calc
      y⊓(x⊔z)⊔y \ x⊓y \ z = (y⊓(x⊔z)⊔y \ x)⊓(y⊓(x⊔z)⊔y \ z) := by
        rw [sup_inf_left]
      _ = (y⊓x⊔y⊓z⊔y \ x)⊓(y⊓x⊔y⊓z⊔y \ z) := by
        rw [@inf_sup_left _ _ y]
      _ = (y⊓z⊔(y⊓x⊔y \ x))⊓(y⊓x⊔(y⊓z⊔y \ z)) := by
        ac_rfl
      _ = (y⊓z⊔y)⊓(y⊓x⊔y) := by
        rw [sup_inf_sdiff, sup_inf_sdiff]
      _ = (y⊔y⊓z)⊓(y⊔y⊓x) := by
        ac_rfl
      _ = y := by
        rw [sup_inf_self, sup_inf_self, inf_idem]
      )
    (calc
      y⊓(x⊔z)⊓(y \ x⊓y \ z) = (y⊓x⊔y⊓z)⊓(y \ x⊓y \ z) := by
        rw [inf_sup_left]
      _ = y⊓x⊓(y \ x⊓y \ z)⊔y⊓z⊓(y \ x⊓y \ z) := by
        rw [inf_sup_right]
      _ = y⊓x⊓y \ x⊓y \ z⊔y \ x⊓(y \ z⊓(y⊓z)) := by
        ac_rfl
      _ = ⊥ := by
        rw [inf_inf_sdiff, bot_inf_eq, bot_sup_eq, @inf_comm _ _ (y \ z), inf_inf_sdiff, inf_bot_eq]
      )

theorem sdiff_eq_sdiff_iff_inf_eq_inf : y \ x = y \ z ↔ y⊓x = y⊓z :=
  ⟨fun h =>
    eq_of_inf_eq_sup_eq
      (by
        rw [inf_inf_sdiff, h, inf_inf_sdiff])
      (by
        rw [sup_inf_sdiff, h, sup_inf_sdiff]),
    fun h => by
    rw [← sdiff_inf_self_right, ← sdiff_inf_self_right z y, inf_comm, h, inf_comm]⟩

theorem Disjoint.sdiff_eq_left (h : Disjoint x y) : x \ y = x := by
  conv_rhs => rw [← sup_inf_sdiff x y, h.eq_bot, bot_sup_eq]

theorem Disjoint.sdiff_eq_right (h : Disjoint x y) : y \ x = y :=
  h.symm.sdiff_eq_left

theorem sdiff_eq_self_iff_disjoint : x \ y = x ↔ Disjoint y x :=
  calc
    x \ y = x ↔ x \ y = x \ ⊥ := by
      rw [sdiff_bot]
    _ ↔ x⊓y = x⊓⊥ := sdiff_eq_sdiff_iff_inf_eq_inf
    _ ↔ Disjoint y x := by
      rw [inf_bot_eq, inf_comm, disjoint_iff]
    

theorem sdiff_eq_self_iff_disjoint' : x \ y = x ↔ Disjoint x y := by
  rw [sdiff_eq_self_iff_disjoint, Disjoint.comm]

theorem sdiff_lt (hx : y ≤ x) (hy : y ≠ ⊥) : x \ y < x := by
  refine' sdiff_le.lt_of_ne fun h => hy _
  rw [sdiff_eq_self_iff_disjoint', disjoint_iff] at h
  rw [← h, inf_eq_right.mpr hx]

theorem sdiff_sdiff_le : x \ (x \ y) ≤ y :=
  sdiff_le_iff.2 le_sdiff_sup

theorem sdiff_triangle (x y z : α) : x \ z ≤ x \ y⊔y \ z := by
  rw [sdiff_le_iff, sup_left_comm, ← sdiff_le_iff]
  exact sdiff_sdiff_le.trans (sdiff_le_iff.1 le_rflₓ)

@[simp]
theorem le_sdiff_iff : x ≤ y \ x ↔ x = ⊥ :=
  ⟨fun h => disjoint_self.1 (disjoint_sdiff_self_right.mono_right h), fun h => h.le.trans bot_le⟩

theorem sdiff_lt_sdiff_right (h : x < y) (hz : z ≤ x) : x \ z < y \ z :=
  (sdiff_le_sdiff_right h.le).lt_of_not_le fun h' => h.not_le <| le_sdiff_sup.trans <| sup_le_of_le_sdiff_right h' hz

theorem sup_inf_inf_sdiff : x⊓y⊓z⊔y \ z = x⊓y⊔y \ z :=
  calc
    x⊓y⊓z⊔y \ z = x⊓(y⊓z)⊔y \ z := by
      rw [inf_assoc]
    _ = (x⊔y \ z)⊓y := by
      rw [sup_inf_right, sup_inf_sdiff]
    _ = x⊓y⊔y \ z := by
      rw [inf_sup_right, inf_sdiff_left]
    

@[simp]
theorem inf_sdiff_sup_left : x \ z⊓(x⊔y) = x \ z := by
  rw [inf_sup_left, inf_sdiff_left, sup_inf_self]

@[simp]
theorem inf_sdiff_sup_right : x \ z⊓(y⊔x) = x \ z := by
  rw [sup_comm, inf_sdiff_sup_left]

theorem sdiff_sdiff_right : x \ (y \ z) = x \ y⊔x⊓y⊓z := by
  rw [sup_comm, inf_comm, ← inf_assoc, sup_inf_inf_sdiff]
  apply sdiff_unique
  · calc
      x⊓y \ z⊔(z⊓x⊔x \ y) = (x⊔(z⊓x⊔x \ y))⊓(y \ z⊔(z⊓x⊔x \ y)) := by
        rw [sup_inf_right]
      _ = (x⊔x⊓z⊔x \ y)⊓(y \ z⊔(x⊓z⊔x \ y)) := by
        ac_rfl
      _ = x⊓(y \ z⊔x⊓z⊔x \ y) := by
        rw [sup_inf_self, sup_sdiff_left, ← sup_assoc]
      _ = x⊓(y \ z⊓(z⊔y)⊔x⊓(z⊔y)⊔x \ y) := by
        rw [sup_inf_left, sup_sdiff_self_left, inf_sup_right, @sup_comm _ _ y]
      _ = x⊓(y \ z⊔(x⊓z⊔x⊓y)⊔x \ y) := by
        rw [inf_sdiff_sup_right, @inf_sup_left _ _ x z y]
      _ = x⊓(y \ z⊔(x⊓z⊔(x⊓y⊔x \ y))) := by
        ac_rfl
      _ = x⊓(y \ z⊔(x⊔x⊓z)) := by
        rw [sup_inf_sdiff, @sup_comm _ _ (x⊓z)]
      _ = x := by
        rw [sup_inf_self, sup_comm, inf_sup_self]
      
    
  · calc
      x⊓y \ z⊓(z⊓x⊔x \ y) = x⊓y \ z⊓(z⊓x)⊔x⊓y \ z⊓x \ y := by
        rw [inf_sup_left]
      _ = x⊓(y \ z⊓z⊓x)⊔x⊓y \ z⊓x \ y := by
        ac_rfl
      _ = x⊓y \ z⊓x \ y := by
        rw [inf_sdiff_self_left, bot_inf_eq, inf_bot_eq, bot_sup_eq]
      _ = x⊓(y \ z⊓y)⊓x \ y := by
        conv_lhs => rw [← inf_sdiff_left]
      _ = x⊓(y \ z⊓(y⊓x \ y)) := by
        ac_rfl
      _ = ⊥ := by
        rw [inf_sdiff_self_right, inf_bot_eq, inf_bot_eq]
      
    

theorem sdiff_sdiff_right' : x \ (y \ z) = x \ y⊔x⊓z :=
  calc
    x \ (y \ z) = x \ y⊔x⊓y⊓z := sdiff_sdiff_right
    _ = z⊓x⊓y⊔x \ y := by
      ac_rfl
    _ = x \ y⊔x⊓z := by
      rw [sup_inf_inf_sdiff, sup_comm, inf_comm]
    

theorem sdiff_sdiff_eq_sdiff_sup (h : z ≤ x) : x \ (y \ z) = x \ y⊔z := by
  rw [sdiff_sdiff_right', inf_eq_right.2 h]

@[simp]
theorem sdiff_sdiff_right_self : x \ (x \ y) = x⊓y := by
  rw [sdiff_sdiff_right, inf_idem, sdiff_self, bot_sup_eq]

theorem sdiff_sdiff_eq_self (h : y ≤ x) : x \ (x \ y) = y := by
  rw [sdiff_sdiff_right_self, inf_of_le_right h]

theorem sdiff_eq_symm (hy : y ≤ x) (h : x \ y = z) : x \ z = y := by
  rw [← h, sdiff_sdiff_eq_self hy]

theorem sdiff_eq_comm (hy : y ≤ x) (hz : z ≤ x) : x \ y = z ↔ x \ z = y :=
  ⟨sdiff_eq_symm hy, sdiff_eq_symm hz⟩

theorem eq_of_sdiff_eq_sdiff (hxz : x ≤ z) (hyz : y ≤ z) (h : z \ x = z \ y) : x = y := by
  rw [← sdiff_sdiff_eq_self hxz, h, sdiff_sdiff_eq_self hyz]

theorem sdiff_sdiff_left : (x \ y) \ z = x \ (y⊔z) := by
  rw [sdiff_sup]
  apply sdiff_unique
  · rw [← inf_sup_left, sup_sdiff_self_right, inf_sdiff_sup_right]
    
  · rw [inf_assoc, @inf_comm _ _ z, inf_assoc, inf_sdiff_self_left, inf_bot_eq, inf_bot_eq]
    

theorem sdiff_sdiff_left' : (x \ y) \ z = x \ y⊓x \ z := by
  rw [sdiff_sdiff_left, sdiff_sup]

theorem sdiff_sdiff_comm : (x \ y) \ z = (x \ z) \ y := by
  rw [sdiff_sdiff_left, sup_comm, sdiff_sdiff_left]

@[simp]
theorem sdiff_idem : (x \ y) \ y = x \ y := by
  rw [sdiff_sdiff_left, sup_idem]

@[simp]
theorem sdiff_sdiff_self : (x \ y) \ x = ⊥ := by
  rw [sdiff_sdiff_comm, sdiff_self, bot_sdiff]

theorem sdiff_sdiff_sup_sdiff : z \ (x \ y⊔y \ x) = z⊓(z \ x⊔y)⊓(z \ y⊔x) :=
  calc
    z \ (x \ y⊔y \ x) = (z \ x⊔z⊓x⊓y)⊓(z \ y⊔z⊓y⊓x) := by
      rw [sdiff_sup, sdiff_sdiff_right, sdiff_sdiff_right]
    _ = z⊓(z \ x⊔y)⊓(z \ y⊔z⊓y⊓x) := by
      rw [sup_inf_left, sup_comm, sup_inf_sdiff]
    _ = z⊓(z \ x⊔y)⊓(z⊓(z \ y⊔x)) := by
      rw [sup_inf_left, @sup_comm _ _ (z \ y), sup_inf_sdiff]
    _ = z⊓z⊓(z \ x⊔y)⊓(z \ y⊔x) := by
      ac_rfl
    _ = z⊓(z \ x⊔y)⊓(z \ y⊔x) := by
      rw [inf_idem]
    

theorem sdiff_sdiff_sup_sdiff' : z \ (x \ y⊔y \ x) = z⊓x⊓y⊔z \ x⊓z \ y :=
  calc
    z \ (x \ y⊔y \ x) = z \ (x \ y)⊓z \ (y \ x) := sdiff_sup
    _ = (z \ x⊔z⊓x⊓y)⊓(z \ y⊔z⊓y⊓x) := by
      rw [sdiff_sdiff_right, sdiff_sdiff_right]
    _ = (z \ x⊔z⊓y⊓x)⊓(z \ y⊔z⊓y⊓x) := by
      ac_rfl
    _ = z \ x⊓z \ y⊔z⊓y⊓x := sup_inf_right.symm
    _ = z⊓x⊓y⊔z \ x⊓z \ y := by
      ac_rfl
    

theorem sup_sdiff : (x⊔y) \ z = x \ z⊔y \ z :=
  sdiff_unique
    (calc
      (x⊔y)⊓z⊔(x \ z⊔y \ z) = x⊓z⊔y⊓z⊔(x \ z⊔y \ z) := by
        rw [inf_sup_right]
      _ = x⊓z⊔x \ z⊔y \ z⊔y⊓z := by
        ac_rfl
      _ = x⊔(y⊓z⊔y \ z) := by
        rw [sup_inf_sdiff, sup_assoc, @sup_comm _ _ (y \ z)]
      _ = x⊔y := by
        rw [sup_inf_sdiff]
      )
    (calc
      (x⊔y)⊓z⊓(x \ z⊔y \ z) = (x⊓z⊔y⊓z)⊓(x \ z⊔y \ z) := by
        rw [inf_sup_right]
      _ = (x⊓z⊔y⊓z)⊓x \ z⊔(x⊓z⊔y⊓z)⊓y \ z := by
        rw [@inf_sup_left _ _ (x⊓z⊔y⊓z)]
      _ = y⊓z⊓x \ z⊔(x⊓z⊔y⊓z)⊓y \ z := by
        rw [inf_sup_right, inf_inf_sdiff, bot_sup_eq]
      _ = (x⊓z⊔y⊓z)⊓y \ z := by
        rw [inf_assoc, inf_sdiff_self_right, inf_bot_eq, bot_sup_eq]
      _ = x⊓z⊓y \ z := by
        rw [inf_sup_right, inf_inf_sdiff, sup_bot_eq]
      _ = ⊥ := by
        rw [inf_assoc, inf_sdiff_self_right, inf_bot_eq]
      )

theorem sup_sdiff_right_self : (x⊔y) \ y = x \ y := by
  rw [sup_sdiff, sdiff_self, sup_bot_eq]

theorem sup_sdiff_left_self : (x⊔y) \ x = y \ x := by
  rw [sup_comm, sup_sdiff_right_self]

theorem inf_sdiff : (x⊓y) \ z = x \ z⊓y \ z :=
  sdiff_unique
    (calc
      x⊓y⊓z⊔x \ z⊓y \ z = (x⊓y⊓z⊔x \ z)⊓(x⊓y⊓z⊔y \ z) := by
        rw [sup_inf_left]
      _ = (x⊓y⊓(z⊔x)⊔x \ z)⊓(x⊓y⊓z⊔y \ z) := by
        rw [sup_inf_right, sup_sdiff_self_right, inf_sup_right, inf_sdiff_sup_right]
      _ = (y⊓(x⊓(x⊔z))⊔x \ z)⊓(x⊓y⊓z⊔y \ z) := by
        ac_rfl
      _ = (y⊓x⊔x \ z)⊓(x⊓y⊔y \ z) := by
        rw [inf_sup_self, sup_inf_inf_sdiff]
      _ = x⊓y⊔x \ z⊓y \ z := by
        rw [@inf_comm _ _ y, sup_inf_left]
      _ = x⊓y := sup_eq_left.2 (inf_le_inf sdiff_le sdiff_le)
      )
    (calc
      x⊓y⊓z⊓(x \ z⊓y \ z) = x⊓y⊓(z⊓x \ z)⊓y \ z := by
        ac_rfl
      _ = ⊥ := by
        rw [inf_sdiff_self_right, inf_bot_eq, bot_inf_eq]
      )

theorem inf_sdiff_assoc : (x⊓y) \ z = x⊓y \ z :=
  sdiff_unique
    (calc
      x⊓y⊓z⊔x⊓y \ z = x⊓(y⊓z)⊔x⊓y \ z := by
        rw [inf_assoc]
      _ = x⊓(y⊓z⊔y \ z) := inf_sup_left.symm
      _ = x⊓y := by
        rw [sup_inf_sdiff]
      )
    (calc
      x⊓y⊓z⊓(x⊓y \ z) = x⊓x⊓(y⊓z⊓y \ z) := by
        ac_rfl
      _ = ⊥ := by
        rw [inf_inf_sdiff, inf_bot_eq]
      )

theorem inf_sdiff_right_comm : x \ z⊓y = (x⊓y) \ z := by
  rw [@inf_comm _ _ x, inf_comm, inf_sdiff_assoc]

theorem inf_sdiff_distrib_left (a b c : α) : a⊓b \ c = (a⊓b) \ (a⊓c) := by
  rw [sdiff_inf, sdiff_eq_bot_iff.2 inf_le_left, bot_sup_eq, inf_sdiff_assoc]

theorem inf_sdiff_distrib_right (a b c : α) : a \ b⊓c = (a⊓c) \ (b⊓c) := by
  simp_rw [@inf_comm _ _ _ c, inf_sdiff_distrib_left]

theorem sdiff_sup_sdiff_cancel (hyx : y ≤ x) (hzy : z ≤ y) : x \ y⊔y \ z = x \ z := by
  rw [← sup_sdiff_inf (x \ z) y, sdiff_sdiff_left, sup_eq_right.2 hzy, inf_sdiff_right_comm, inf_eq_right.2 hyx]

theorem sup_eq_sdiff_sup_sdiff_sup_inf : x⊔y = x \ y⊔y \ x⊔x⊓y :=
  Eq.symm <|
    calc
      x \ y⊔y \ x⊔x⊓y = (x \ y⊔y \ x⊔x)⊓(x \ y⊔y \ x⊔y) := by
        rw [sup_inf_left]
      _ = (x \ y⊔x⊔y \ x)⊓(x \ y⊔(y \ x⊔y)) := by
        ac_rfl
      _ = (x⊔y \ x)⊓(x \ y⊔y) := by
        rw [sup_sdiff_right, sup_sdiff_right]
      _ = x⊔y := by
        rw [sup_sdiff_self_right, sup_sdiff_self_left, inf_idem]
      

theorem sdiff_le_sdiff_of_sup_le_sup_left (h : z⊔x ≤ z⊔y) : x \ z ≤ y \ z := by
  rw [← sup_sdiff_left_self, ← @sup_sdiff_left_self _ _ y]
  exact sdiff_le_sdiff_right h

theorem sdiff_le_sdiff_of_sup_le_sup_right (h : x⊔z ≤ y⊔z) : x \ z ≤ y \ z := by
  rw [← sup_sdiff_right_self, ← @sup_sdiff_right_self _ y]
  exact sdiff_le_sdiff_right h

theorem sup_lt_of_lt_sdiff_left (h : y < z \ x) (hxz : x ≤ z) : x⊔y < z := by
  rw [← sup_sdiff_cancel_right hxz]
  refine' (sup_le_sup_left h.le _).lt_of_not_le fun h' => h.not_le _
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_left h').trans sdiff_le

theorem sup_lt_of_lt_sdiff_right (h : x < z \ y) (hyz : y ≤ z) : x⊔y < z := by
  rw [← sdiff_sup_cancel hyz]
  refine' (sup_le_sup_right h.le _).lt_of_not_le fun h' => h.not_le _
  rw [← sdiff_idem]
  exact (sdiff_le_sdiff_of_sup_le_sup_right h').trans sdiff_le

instance Pi.generalizedBooleanAlgebra {α : Type u} {β : Type v} [GeneralizedBooleanAlgebra β] :
    GeneralizedBooleanAlgebra (α → β) := by
  pi_instance

end GeneralizedBooleanAlgebra

/-!
### Boolean algebras
-/


/-- A Boolean algebra is a bounded distributive lattice with a complement operator `ᶜ` such that
`x ⊓ xᶜ = ⊥` and `x ⊔ xᶜ = ⊤`. For convenience, it must also provide a set difference operation `\`
and a Heyting implication `⇨` satisfying `x \ y = x ⊓ yᶜ` and `x ⇨ y = y ⊔ xᶜ`.

This is a generalization of (classical) logic of propositions, or the powerset lattice.

Since `bounded_order`, `order_bot`, and `order_top` are mixins that require `has_le`
to be present at define-time, the `extends` mechanism does not work with them.
Instead, we extend using the underlying `has_bot` and `has_top` data typeclasses, and replicate the
order axioms of those classes here. A "forgetful" instance back to `bounded_order` is provided.
-/
class BooleanAlgebra (α : Type u) extends DistribLattice α, HasCompl α, Sdiff α, HasHimp α, HasTop α, HasBot α where
  inf_compl_le_bot : ∀ x : α, x⊓xᶜ ≤ ⊥
  top_le_sup_compl : ∀ x : α, ⊤ ≤ x⊔xᶜ
  le_top : ∀ a : α, a ≤ ⊤
  bot_le : ∀ a : α, ⊥ ≤ a
  sdiff := fun x y => x⊓yᶜ
  himp := fun x y => y⊔xᶜ
  sdiff_eq : ∀ x y : α, x \ y = x⊓yᶜ := by
    run_tac
      obviously
  himp_eq : ∀ x y : α, x ⇨ y = y⊔xᶜ := by
    run_tac
      obviously

-- see Note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toBoundedOrder [h : BooleanAlgebra α] : BoundedOrder α :=
  { h with }

-- See note [reducible non instances]
/-- A bounded generalized boolean algebra is a boolean algebra. -/
@[reducible]
def GeneralizedBooleanAlgebra.toBooleanAlgebra [GeneralizedBooleanAlgebra α] [OrderTop α] : BooleanAlgebra α :=
  { ‹GeneralizedBooleanAlgebra α›, GeneralizedBooleanAlgebra.toOrderBot, ‹OrderTop α› with compl := fun a => ⊤ \ a,
    inf_compl_le_bot := fun _ => disjoint_sdiff_self_right, top_le_sup_compl := fun _ => le_sup_sdiff,
    sdiff_eq := fun _ _ => by
      rw [← inf_sdiff_assoc, inf_top_eq]
      rfl }

section BooleanAlgebra

variable [BooleanAlgebra α]

@[simp]
theorem inf_compl_eq_bot' : x⊓xᶜ = ⊥ :=
  bot_unique <| BooleanAlgebra.inf_compl_le_bot x

@[simp]
theorem sup_compl_eq_top : x⊔xᶜ = ⊤ :=
  top_unique <| BooleanAlgebra.top_le_sup_compl x

@[simp]
theorem compl_sup_eq_top : xᶜ⊔x = ⊤ :=
  sup_comm.trans sup_compl_eq_top

theorem is_compl_compl : IsCompl x (xᶜ) :=
  IsCompl.of_eq inf_compl_eq_bot' sup_compl_eq_top

theorem sdiff_eq : x \ y = x⊓yᶜ :=
  BooleanAlgebra.sdiff_eq x y

theorem himp_eq : x ⇨ y = y⊔xᶜ :=
  BooleanAlgebra.himp_eq x y

@[simp]
theorem top_sdiff : ⊤ \ x = xᶜ := by
  rw [sdiff_eq, top_inf_eq]

instance (priority := 100) BooleanAlgebra.to_is_complemented : IsComplemented α :=
  ⟨fun x => ⟨xᶜ, is_compl_compl⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toGeneralizedBooleanAlgebra : GeneralizedBooleanAlgebra α :=
  { ‹BooleanAlgebra α› with
    sup_inf_sdiff := fun a b => by
      rw [sdiff_eq, ← inf_sup_left, sup_compl_eq_top, inf_top_eq],
    inf_inf_sdiff := fun a b => by
      rw [sdiff_eq, ← inf_inf_distrib_left, inf_compl_eq_bot', inf_bot_eq]
      congr }

-- See note [lower instance priority]
instance (priority := 100) BooleanAlgebra.toBiheytingAlgebra : BiheytingAlgebra α :=
  { ‹BooleanAlgebra α›, GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra with hnot := compl,
    le_himp_iff := fun a b c => by
      rw [himp_eq, is_compl_compl.le_sup_right_iff_inf_left_le],
    himp_bot := fun _ => himp_eq.trans bot_sup_eq,
    top_sdiff := fun a => by
      rw [sdiff_eq, top_inf_eq] }

@[simp]
theorem hnot_eq_compl : ￢x = xᶜ :=
  rfl

theorem IsCompl.eq_compl (h : IsCompl x y) : x = yᶜ :=
  h.LeftUnique is_compl_compl.symm

theorem IsCompl.compl_eq (h : IsCompl x y) : xᶜ = y :=
  (h.RightUnique is_compl_compl).symm

theorem eq_compl_iff_is_compl : x = yᶜ ↔ IsCompl x y :=
  ⟨fun h => by
    rw [h]
    exact is_compl_compl.symm, IsCompl.eq_compl⟩

theorem compl_eq_iff_is_compl : xᶜ = y ↔ IsCompl x y :=
  ⟨fun h => by
    rw [← h]
    exact is_compl_compl, IsCompl.compl_eq⟩

theorem compl_eq_comm : xᶜ = y ↔ yᶜ = x := by
  rw [eq_comm, compl_eq_iff_is_compl, eq_compl_iff_is_compl]

theorem eq_compl_comm : x = yᶜ ↔ y = xᶜ := by
  rw [eq_comm, compl_eq_iff_is_compl, eq_compl_iff_is_compl]

theorem compl_unique (i : x⊓y = ⊥) (s : x⊔y = ⊤) : xᶜ = y :=
  (IsCompl.of_eq i s).compl_eq

@[simp]
theorem compl_compl (x : α) : xᶜᶜ = x :=
  is_compl_compl.symm.compl_eq

theorem compl_comp_compl : compl ∘ compl = @id α :=
  funext compl_compl

@[simp]
theorem compl_involutive : Function.Involutive (compl : α → α) :=
  compl_compl

theorem compl_bijective : Function.Bijective (compl : α → α) :=
  compl_involutive.Bijective

theorem compl_surjective : Function.Surjective (compl : α → α) :=
  compl_involutive.Surjective

theorem compl_injective : Function.Injective (compl : α → α) :=
  compl_involutive.Injective

@[simp]
theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
  compl_injective.eq_iff

theorem IsCompl.compl_eq_iff (h : IsCompl x y) : zᶜ = y ↔ z = x :=
  h.compl_eq ▸ compl_inj_iff

@[simp]
theorem compl_eq_top : xᶜ = ⊤ ↔ x = ⊥ :=
  is_compl_bot_top.compl_eq_iff

@[simp]
theorem compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤ :=
  is_compl_top_bot.compl_eq_iff

@[simp]
theorem compl_inf : (x⊓y)ᶜ = xᶜ⊔yᶜ :=
  (is_compl_compl.inf_sup is_compl_compl).compl_eq

@[simp]
theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
  ⟨fun h => by
    have h := compl_le_compl h <;> simp at h <;> assumption, compl_le_compl⟩

theorem le_compl_of_le_compl (h : y ≤ xᶜ) : x ≤ yᶜ := by
  simpa only [compl_compl] using compl_le_compl h

theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y := by
  simpa only [compl_compl] using compl_le_compl h

theorem le_compl_iff_le_compl : y ≤ xᶜ ↔ x ≤ yᶜ :=
  ⟨le_compl_of_le_compl, le_compl_of_le_compl⟩

theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
  ⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

@[simp]
theorem sdiff_compl : x \ yᶜ = x⊓y := by
  rw [sdiff_eq, compl_compl]

instance : BooleanAlgebra αᵒᵈ :=
  { OrderDual.distribLattice α, OrderDual.boundedOrder α with compl := fun a => toDual (ofDual aᶜ),
    sdiff := fun a b => toDual (ofDual b ⇨ ofDual a), himp := fun a b => toDual (ofDual b \ ofDual a),
    inf_compl_le_bot := fun a => @codisjoint_hnot_right _ _ (ofDual a),
    top_le_sup_compl := fun a => @disjoint_compl_right _ _ (ofDual a), sdiff_eq := fun _ _ => himp_eq,
    himp_eq := fun _ _ => sdiff_eq }

@[simp]
theorem sup_inf_inf_compl : x⊓y⊔x⊓yᶜ = x := by
  rw [← sdiff_eq, sup_inf_sdiff _ _]

@[simp]
theorem compl_sdiff : (x \ y)ᶜ = xᶜ⊔y := by
  rw [sdiff_eq, compl_inf, compl_compl]

theorem disjoint_compl_left_iff : Disjoint (xᶜ) y ↔ y ≤ x := by
  rw [← le_compl_iff_disjoint_left, compl_compl]

theorem disjoint_compl_right_iff : Disjoint x (yᶜ) ↔ x ≤ y := by
  rw [← le_compl_iff_disjoint_right, compl_compl]

alias disjoint_compl_left_iff ↔ _ LE.le.disjoint_compl_left

alias disjoint_compl_right_iff ↔ _ LE.le.disjoint_compl_right

end BooleanAlgebra

instance Prop.booleanAlgebra : BooleanAlgebra Prop :=
  { Prop.heytingAlgebra, GeneralizedHeytingAlgebra.toDistribLattice with compl := Not,
    himp_eq := fun p q => propext imp_iff_or_not, inf_compl_le_bot := fun p ⟨Hp, Hpc⟩ => Hpc Hp,
    top_le_sup_compl := fun p H => Classical.em p }

instance Pi.booleanAlgebra {ι : Type u} {α : ι → Type v} [∀ i, BooleanAlgebra (α i)] : BooleanAlgebra (∀ i, α i) :=
  { Pi.hasSdiff, Pi.heytingAlgebra, Pi.distribLattice with sdiff_eq := fun x y => funext fun i => sdiff_eq,
    himp_eq := fun x y => funext fun i => himp_eq, inf_compl_le_bot := fun _ _ => BooleanAlgebra.inf_compl_le_bot _,
    top_le_sup_compl := fun _ _ => BooleanAlgebra.top_le_sup_compl _ }

instance : BooleanAlgebra Bool :=
  { Bool.linearOrder, Bool.boundedOrder with sup := bor, le_sup_left := Bool.left_le_bor,
    le_sup_right := Bool.right_le_bor, sup_le := fun _ _ _ => Bool.bor_le, inf := band,
    inf_le_left := Bool.band_le_left, inf_le_right := Bool.band_le_right, le_inf := fun _ _ _ => Bool.le_band,
    le_sup_inf := by
      decide,
    compl := bnot, inf_compl_le_bot := fun a => a.band_bnot_self.le, top_le_sup_compl := fun a => a.bor_bnot_self.Ge }

@[simp]
theorem Bool.sup_eq_bor : (·⊔·) = bor :=
  rfl

@[simp]
theorem Bool.inf_eq_band : (·⊓·) = band :=
  rfl

@[simp]
theorem Bool.compl_eq_bnot : HasCompl.compl = bnot :=
  rfl

section lift

-- See note [reducible non-instances]
/-- Pullback a `generalized_boolean_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.generalizedBooleanAlgebra [HasSup α] [HasInf α] [HasBot α] [Sdiff α]
    [GeneralizedBooleanAlgebra β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedBooleanAlgebra α :=
  { hf.GeneralizedCoheytingAlgebra f map_sup map_inf map_bot map_sdiff, hf.DistribLattice f map_sup map_inf with
    sup_inf_sdiff := fun a b =>
      hf <| by
        erw [map_sup, map_sdiff, map_inf, sup_inf_sdiff],
    inf_inf_sdiff := fun a b =>
      hf <| by
        erw [map_inf, map_sdiff, map_inf, inf_inf_sdiff, map_bot] }

-- See note [reducible non-instances]
/-- Pullback a `boolean_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.booleanAlgebra [HasSup α] [HasInf α] [HasTop α] [HasBot α] [HasCompl α] [Sdiff α]
    [BooleanAlgebra β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f (aᶜ) = f aᶜ)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : BooleanAlgebra α :=
  { hf.GeneralizedBooleanAlgebra f map_sup map_inf map_bot map_sdiff with compl := compl, top := ⊤,
    le_top := fun a => (@le_top β _ _ _).trans map_top.Ge, bot_le := fun a => map_bot.le.trans bot_le,
    inf_compl_le_bot := fun a =>
      ((map_inf _ _).trans <| by
          rw [map_compl, inf_compl_eq_bot, map_bot]).le,
    top_le_sup_compl := fun a =>
      ((map_sup _ _).trans <| by
          rw [map_compl, sup_compl_eq_top, map_top]).Ge,
    sdiff_eq := fun a b =>
      hf <|
        (map_sdiff _ _).trans <|
          sdiff_eq.trans <| by
            convert (map_inf _ _).symm
            exact (map_compl _).symm }

end lift

instance : BooleanAlgebra PUnit := by
  refine_struct { PUnit.biheytingAlgebra with } <;>
    intros <;>
      first |
        trivial|
        exact Subsingleton.elimₓ _ _

