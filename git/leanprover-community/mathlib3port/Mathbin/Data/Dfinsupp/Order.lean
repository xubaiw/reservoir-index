/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Dfinsupp.Basic

/-!
# Pointwise order on finitely supported dependent functions

This file lifts order structures on the `α i` to `Π₀ i, α i`.

## Main declarations

* `dfinsupp.order_embedding_to_fun`: The order embedding from finitely supported dependent functions
  to functions.

## TODO

Add `is_well_order (Π₀ i, α i) (<)`.
-/


open BigOperators

open Finset

variable {ι : Type _} {α : ι → Type _}

namespace Dfinsupp

/-! ### Order structures -/


section Zero

variable (α) [∀ i, Zero (α i)]

section LE

variable [∀ i, LE (α i)]

instance : LE (Π₀ i, α i) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

variable {α}

theorem le_def {f g : Π₀ i, α i} : f ≤ g ↔ ∀ i, f i ≤ g i :=
  Iff.rfl

/-- The order on `dfinsupp`s over a partial order embeds into the order on functions -/
def orderEmbeddingToFun : (Π₀ i, α i) ↪o ∀ i, α i where
  toFun := fun f => f
  inj' := fun f g h =>
    Dfinsupp.ext fun i => by
      dsimp'  at h
      rw [h]
  map_rel_iff' := fun a b => (@le_def _ _ _ _ a b).symm

@[simp]
theorem order_embedding_to_fun_apply {f : Π₀ i, α i} {i : ι} : orderEmbeddingToFun f i = f i :=
  rfl

end LE

section Preorderₓ

variable [∀ i, Preorderₓ (α i)]

instance : Preorderₓ (Π₀ i, α i) :=
  { Dfinsupp.hasLe α with le_refl := fun f i => le_rfl, le_trans := fun f g h hfg hgh i => (hfg i).trans (hgh i) }

theorem coe_fn_mono : Monotone (coeFn : (Π₀ i, α i) → ∀ i, α i) := fun f g => le_def.1

end Preorderₓ

instance [∀ i, PartialOrderₓ (α i)] : PartialOrderₓ (Π₀ i, α i) :=
  { Dfinsupp.preorder α with le_antisymm := fun f g hfg hgf => ext fun i => (hfg i).antisymm (hgf i) }

instance [∀ i, SemilatticeInf (α i)] : SemilatticeInf (Π₀ i, α i) :=
  { Dfinsupp.partialOrder α with inf := zipWith (fun _ => (·⊓·)) fun _ => inf_idem,
    inf_le_left := fun f g i => by
      rw [zip_with_apply]
      exact inf_le_left,
    inf_le_right := fun f g i => by
      rw [zip_with_apply]
      exact inf_le_right,
    le_inf := fun f g h hf hg i => by
      rw [zip_with_apply]
      exact le_inf (hf i) (hg i) }

@[simp]
theorem inf_apply [∀ i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι) : (f⊓g) i = f i⊓g i :=
  zip_with_apply _ _ _ _ _

instance [∀ i, SemilatticeSup (α i)] : SemilatticeSup (Π₀ i, α i) :=
  { Dfinsupp.partialOrder α with sup := zipWith (fun _ => (·⊔·)) fun _ => sup_idem,
    le_sup_left := fun f g i => by
      rw [zip_with_apply]
      exact le_sup_left,
    le_sup_right := fun f g i => by
      rw [zip_with_apply]
      exact le_sup_right,
    sup_le := fun f g h hf hg i => by
      rw [zip_with_apply]
      exact sup_le (hf i) (hg i) }

@[simp]
theorem sup_apply [∀ i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι) : (f⊔g) i = f i⊔g i :=
  zip_with_apply _ _ _ _ _

instance lattice [∀ i, Lattice (α i)] : Lattice (Π₀ i, α i) :=
  { Dfinsupp.semilatticeInf α, Dfinsupp.semilatticeSup α with }

end Zero

/-! ### Algebraic order structures -/


instance (α : ι → Type _) [∀ i, OrderedAddCommMonoid (α i)] : OrderedAddCommMonoid (Π₀ i, α i) :=
  { Dfinsupp.addCommMonoid, Dfinsupp.partialOrder α with
    add_le_add_left := fun a b h c i => by
      rw [add_apply, add_apply]
      exact add_le_add_left (h i) (c i) }

instance (α : ι → Type _) [∀ i, OrderedCancelAddCommMonoid (α i)] : OrderedCancelAddCommMonoid (Π₀ i, α i) :=
  { Dfinsupp.orderedAddCommMonoid α with
    le_of_add_le_add_left := fun f g h H i => by
      specialize H i
      rw [add_apply, add_apply] at H
      exact le_of_add_le_add_left H,
    add_left_cancel := fun f g h H =>
      ext fun i => by
        refine' add_left_cancelₓ _
        exact f i
        rw [← add_apply, ← add_apply, H] }

instance [∀ i, OrderedAddCommMonoid (α i)] [∀ i, ContravariantClass (α i) (α i) (· + ·) (· ≤ ·)] :
    ContravariantClass (Π₀ i, α i) (Π₀ i, α i) (· + ·) (· ≤ ·) :=
  ⟨fun f g h H i => by
    specialize H i
    rw [add_apply, add_apply] at H
    exact le_of_add_le_add_left H⟩

section CanonicallyOrderedAddMonoid

variable (α) [∀ i, CanonicallyOrderedAddMonoid (α i)]

instance : OrderBot (Π₀ i, α i) where
  bot := 0
  bot_le := by
    simp only [le_def, coe_zero, Pi.zero_apply, implies_true_iff, zero_le]

variable {α}

protected theorem bot_eq_zero : (⊥ : Π₀ i, α i) = 0 :=
  rfl

@[simp]
theorem add_eq_zero_iff (f g : Π₀ i, α i) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [ext_iff, forall_and_distrib]

section Le

variable [DecidableEq ι] [∀ i x : α i, Decidable (x ≠ 0)] {f g : Π₀ i, α i} {s : Finset ι}

theorem le_iff' (hf : f.support ⊆ s) : f ≤ g ↔ ∀, ∀ i ∈ s, ∀, f i ≤ g i :=
  ⟨fun h s hs => h s, fun h s =>
    if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩

theorem le_iff : f ≤ g ↔ ∀, ∀ i ∈ f.support, ∀, f i ≤ g i :=
  le_iff' <| Subset.refl _

variable (α)

instance decidableLe [∀ i, DecidableRel (@LE.le (α i) _)] : DecidableRel (@LE.le (Π₀ i, α i) _) := fun f g =>
  decidableOfIff _ le_iff.symm

variable {α}

@[simp]
theorem single_le_iff {i : ι} {a : α i} : single i a ≤ f ↔ a ≤ f i :=
  (le_iff' support_single_subset).trans <| by
    simp

end Le

variable (α) [∀ i, Sub (α i)] [∀ i, HasOrderedSub (α i)] {f g : Π₀ i, α i} {i : ι} {a b : α i}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : Sub (Π₀ i, α i) :=
  ⟨zipWith (fun i m n => m - n) fun i => tsub_self 0⟩

variable {α}

theorem tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = f i - g i :=
  zip_with_apply _ _ _ _ _

@[simp]
theorem coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g := by
  ext i
  exact tsub_apply f g i

variable (α)

instance : HasOrderedSub (Π₀ i, α i) :=
  ⟨fun n m k =>
    forall_congrₓ fun i => by
      rw [add_apply, tsub_apply]
      exact tsub_le_iff_right⟩

instance : CanonicallyOrderedAddMonoid (Π₀ i, α i) :=
  { Dfinsupp.orderBot α, Dfinsupp.orderedAddCommMonoid α with
    le_iff_exists_add := fun f g => by
      refine' ⟨fun h => ⟨g - f, _⟩, _⟩
      · ext i
        rw [add_apply, tsub_apply]
        exact (add_tsub_cancel_of_le <| h i).symm
        
      · rintro ⟨g, rfl⟩ i
        rw [add_apply]
        exact self_le_add_right (f i) (g i)
         }

variable {α} [DecidableEq ι]

@[simp]
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  obtain rfl | h := eq_or_ne i j
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
    
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]
    

variable [∀ i x : α i, Decidable (x ≠ 0)]

theorem support_tsub : (f - g).support ⊆ f.support := by
  simp (config := { contextual := true })only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff, Ne.def, coe_tsub,
    Pi.sub_apply, not_imp_not, zero_le, implies_true_iff]

theorem subset_support_tsub : f.support \ g.support ⊆ (f - g).support := by
  simp (config := { contextual := true })[subset_iff]

end CanonicallyOrderedAddMonoid

section CanonicallyLinearOrderedAddMonoid

variable [∀ i, CanonicallyLinearOrderedAddMonoid (α i)] [DecidableEq ι] {f g : Π₀ i, α i}

@[simp]
theorem support_inf : (f⊓g).support = f.support ∩ g.support := by
  ext
  simp only [inf_apply, mem_support_iff, Ne.def, Finset.mem_union, Finset.mem_filter, Finset.mem_inter]
  simp only [inf_eq_min, ← nonpos_iff_eq_zero, min_le_iff, not_or_distrib]

@[simp]
theorem support_sup : (f⊔g).support = f.support ∪ g.support := by
  ext
  simp only [Finset.mem_union, mem_support_iff, sup_apply, Ne.def, ← bot_eq_zero]
  rw [_root_.sup_eq_bot_iff, not_and_distrib]

theorem disjoint_iff : Disjoint f g ↔ Disjoint f.support g.support := by
  rw [disjoint_iff, disjoint_iff, Dfinsupp.bot_eq_zero, ← Dfinsupp.support_eq_empty, Dfinsupp.support_inf]
  rfl

end CanonicallyLinearOrderedAddMonoid

end Dfinsupp

