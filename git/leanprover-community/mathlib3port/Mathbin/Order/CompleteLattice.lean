/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Bool.Set
import Mathbin.Data.Nat.Basic
import Mathbin.Order.Bounds

/-!
# Theory of complete lattices

## Main definitions

* `Sup` and `Inf` are the supremum and the infimum of a set;
* `supr (f : ι → α)` and `infi (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `Sup` and `Inf` of the range of this function;
* `class complete_lattice`: a bounded lattice such that `Sup s` is always the least upper boundary
  of `s` and `Inf s` is always the greatest lower boundary of `s`;
* `class complete_linear_order`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `Sup` is called `Sup`
* `Inf` is called `Inf`
* `⨆ i, s i` is called `supr`
* `⨅ i, s i` is called `infi`
* `⨆ i j, s i j` is called `supr₂`. This is a `supr` inside a `supr`.
* `⨅ i j, s i j` is called `infi₂`. This is an `infi` inside an `infi`.
* `⨆ i ∈ s, t i` is called `bsupr` for "bounded `supr`". This is the special case of `supr₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `binfi` for "bounded `infi`". This is the special case of `infi₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `supr f`, the supremum of the range of `f`;
* `⨅ i, f i` : `infi f`, the infimum of the range of `f`.
-/


open Set Function

variable {α β β₂ : Type _} {ι ι' : Sort _} {κ : ι → Sort _} {κ' : ι' → Sort _}

/-- class for the `Sup` operator -/
class HasSupₓ (α : Type _) where
  sup : Set α → α

/-- class for the `Inf` operator -/
class HasInfₓ (α : Type _) where
  inf : Set α → α

export HasSupₓ (sup)

export HasInfₓ (inf)

/-- Supremum of a set -/
add_decl_doc HasSupₓ.sup

/-- Infimum of a set -/
add_decl_doc HasInfₓ.inf

/-- Indexed supremum -/
def supr [HasSupₓ α] {ι} (s : ι → α) : α :=
  sup (Range s)

/-- Indexed infimum -/
def infi [HasInfₓ α] {ι} (s : ι → α) : α :=
  inf (Range s)

instance (priority := 50) has_Inf_to_nonempty α [HasInfₓ α] : Nonempty α :=
  ⟨inf ∅⟩

instance (priority := 50) has_Sup_to_nonempty α [HasSupₓ α] : Nonempty α :=
  ⟨sup ∅⟩

-- mathport name: «expr⨆ , »
notation3 "⨆ " (...) ", " r:(scoped f => supr f) => r

-- mathport name: «expr⨅ , »
notation3 "⨅ " (...) ", " r:(scoped f => infi f) => r

instance α [HasInfₓ α] : HasSupₓ (OrderDual α) :=
  ⟨(inf : Set α → α)⟩

instance α [HasSupₓ α] : HasInfₓ (OrderDual α) :=
  ⟨(sup : Set α → α)⟩

/-- Note that we rarely use `complete_semilattice_Sup`
(in fact, any such object is always a `complete_lattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[ancestor PartialOrderₓ HasSupₓ]
class CompleteSemilatticeSup (α : Type _) extends PartialOrderₓ α, HasSupₓ α where
  le_Sup : ∀ s, ∀, ∀ a ∈ s, ∀, a ≤ Sup s
  Sup_le : ∀ s a, (∀, ∀ b ∈ s, ∀, b ≤ a) → Sup s ≤ a

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

@[ematch]
theorem le_Sup : a ∈ s → a ≤ sup s :=
  CompleteSemilatticeSup.le_Sup s a

theorem Sup_le : (∀, ∀ b ∈ s, ∀, b ≤ a) → sup s ≤ a :=
  CompleteSemilatticeSup.Sup_le s a

theorem is_lub_Sup (s : Set α) : IsLub s (sup s) :=
  ⟨fun x => le_Sup, fun x => Sup_le⟩

theorem IsLub.Sup_eq (h : IsLub s a) : sup s = a :=
  (is_lub_Sup s).unique h

theorem le_Sup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ sup s :=
  le_transₓ h (le_Sup hb)

theorem Sup_le_Sup (h : s ⊆ t) : sup s ≤ sup t :=
  (is_lub_Sup s).mono (is_lub_Sup t) h

@[simp]
theorem Sup_le_iff : sup s ≤ a ↔ ∀, ∀ b ∈ s, ∀, b ≤ a :=
  is_lub_le_iff (is_lub_Sup s)

theorem le_Sup_iff : a ≤ sup s ↔ ∀, ∀ b ∈ UpperBounds s, ∀, a ≤ b :=
  ⟨fun h b hb => le_transₓ h (Sup_le hb), fun hb => hb _ fun x => le_Sup⟩

theorem le_supr_iff {s : ι → α} : a ≤ supr s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [supr, le_Sup_iff, UpperBounds]

theorem Sup_le_Sup_of_forall_exists_le (h : ∀, ∀ x ∈ s, ∀, ∃ y ∈ t, x ≤ y) : sup s ≤ sup t :=
  le_Sup_iff.2 fun b hb =>
    Sup_le fun a ha =>
      let ⟨c, hct, hac⟩ := h a ha
      hac.trans (hb hct)

-- We will generalize this to conditionally complete lattices in `cSup_singleton`.
theorem Sup_singleton {a : α} : sup {a} = a :=
  is_lub_singleton.Sup_eq

end

/-- Note that we rarely use `complete_semilattice_Inf`
(in fact, any such object is always a `complete_lattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[ancestor PartialOrderₓ HasInfₓ]
class CompleteSemilatticeInf (α : Type _) extends PartialOrderₓ α, HasInfₓ α where
  Inf_le : ∀ s, ∀, ∀ a ∈ s, ∀, Inf s ≤ a
  le_Inf : ∀ s a, (∀, ∀ b ∈ s, ∀, a ≤ b) → a ≤ Inf s

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

@[ematch]
theorem Inf_le : a ∈ s → inf s ≤ a :=
  CompleteSemilatticeInf.Inf_le s a

theorem le_Inf : (∀, ∀ b ∈ s, ∀, a ≤ b) → a ≤ inf s :=
  CompleteSemilatticeInf.le_Inf s a

theorem is_glb_Inf (s : Set α) : IsGlb s (inf s) :=
  ⟨fun a => Inf_le, fun a => le_Inf⟩

theorem IsGlb.Inf_eq (h : IsGlb s a) : inf s = a :=
  (is_glb_Inf s).unique h

theorem Inf_le_of_le (hb : b ∈ s) (h : b ≤ a) : inf s ≤ a :=
  le_transₓ (Inf_le hb) h

theorem Inf_le_Inf (h : s ⊆ t) : inf t ≤ inf s :=
  (is_glb_Inf s).mono (is_glb_Inf t) h

@[simp]
theorem le_Inf_iff : a ≤ inf s ↔ ∀, ∀ b ∈ s, ∀, a ≤ b :=
  le_is_glb_iff (is_glb_Inf s)

theorem Inf_le_iff : inf s ≤ a ↔ ∀, ∀ b ∈ LowerBounds s, ∀, b ≤ a :=
  ⟨fun h b hb => le_transₓ (le_Inf hb) h, fun hb => hb _ fun x => Inf_le⟩

theorem infi_le_iff {s : ι → α} : infi s ≤ a ↔ ∀ b, (∀ i, b ≤ s i) → b ≤ a := by
  simp [infi, Inf_le_iff, LowerBounds]

theorem Inf_le_Inf_of_forall_exists_le (h : ∀, ∀ x ∈ s, ∀, ∃ y ∈ t, y ≤ x) : inf t ≤ inf s :=
  le_of_forall_le
    (by
      simp only [le_Inf_iff]
      introv h₀ h₁
      rcases h _ h₁ with ⟨y, hy, hy'⟩
      solve_by_elim [le_transₓ _ hy'])

-- We will generalize this to conditionally complete lattices in `cInf_singleton`.
theorem Inf_singleton {a : α} : inf {a} = a :=
  is_glb_singleton.Inf_eq

end

/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
@[protect_proj, ancestor Lattice CompleteSemilatticeSup CompleteSemilatticeInf HasTop HasBot]
class CompleteLattice (α : Type _) extends Lattice α, CompleteSemilatticeSup α, CompleteSemilatticeInf α, HasTop α,
  HasBot α where
  le_top : ∀ x : α, x ≤ ⊤
  bot_le : ∀ x : α, ⊥ ≤ x

-- see Note [lower instance priority]
instance (priority := 100) CompleteLattice.toBoundedOrder [h : CompleteLattice α] : BoundedOrder α :=
  { h with }

/-- Create a `complete_lattice` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup, bot, top
  ..complete_lattice_of_Inf my_T _ }
```
-/
def completeLatticeOfInf (α : Type _) [H1 : PartialOrderₓ α] [H2 : HasInfₓ α]
    (is_glb_Inf : ∀ s : Set α, IsGlb s (inf s)) : CompleteLattice α :=
  { H1, H2 with bot := inf Univ, bot_le := fun x => (is_glb_Inf Univ).1 trivialₓ, top := inf ∅,
    le_top := fun a =>
      (is_glb_Inf ∅).2 <| by
        simp ,
    sup := fun a b => inf { x | a ≤ x ∧ b ≤ x }, inf := fun a b => inf {a, b},
    le_inf := fun a b c hab hac => by
      apply (is_glb_Inf _).2
      simp [*],
    inf_le_right := fun a b => (is_glb_Inf _).1 <| mem_insert_of_mem _ <| mem_singleton _,
    inf_le_left := fun a b => (is_glb_Inf _).1 <| mem_insert _ _,
    sup_le := fun a b c hac hbc =>
      (is_glb_Inf _).1 <| by
        simp [*],
    le_sup_left := fun a b => (is_glb_Inf _).2 fun x => And.left,
    le_sup_right := fun a b => (is_glb_Inf _).2 fun x => And.right, le_Inf := fun s a ha => (is_glb_Inf s).2 ha,
    Inf_le := fun s a ha => (is_glb_Inf s).1 ha, sup := fun s => inf (UpperBounds s),
    le_Sup := fun s a ha => (is_glb_Inf (UpperBounds s)).2 fun b hb => hb ha,
    Sup_le := fun s a ha => (is_glb_Inf (UpperBounds s)).1 ha }

/-- Any `complete_semilattice_Inf` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Inf`.
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type _) [CompleteSemilatticeInf α] : CompleteLattice α :=
  completeLatticeOfInf α fun s => is_glb_Inf s

/-- Create a `complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf, bot, top
  ..complete_lattice_of_Sup my_T _ }
```
-/
def completeLatticeOfSup (α : Type _) [H1 : PartialOrderₓ α] [H2 : HasSupₓ α]
    (is_lub_Sup : ∀ s : Set α, IsLub s (sup s)) : CompleteLattice α :=
  { H1, H2 with top := sup Univ, le_top := fun x => (is_lub_Sup Univ).1 trivialₓ, bot := sup ∅,
    bot_le := fun x =>
      (is_lub_Sup ∅).2 <| by
        simp ,
    sup := fun a b => sup {a, b},
    sup_le := fun a b c hac hbc =>
      (is_lub_Sup _).2
        (by
          simp [*]),
    le_sup_left := fun a b => (is_lub_Sup _).1 <| mem_insert _ _,
    le_sup_right := fun a b => (is_lub_Sup _).1 <| mem_insert_of_mem _ <| mem_singleton _,
    inf := fun a b => sup { x | x ≤ a ∧ x ≤ b },
    le_inf := fun a b c hab hac =>
      (is_lub_Sup _).1 <| by
        simp [*],
    inf_le_left := fun a b => (is_lub_Sup _).2 fun x => And.left,
    inf_le_right := fun a b => (is_lub_Sup _).2 fun x => And.right, inf := fun s => sup (LowerBounds s),
    Sup_le := fun s a ha => (is_lub_Sup s).2 ha, le_Sup := fun s a ha => (is_lub_Sup s).1 ha,
    Inf_le := fun s a ha => (is_lub_Sup (LowerBounds s)).2 fun b hb => hb ha,
    le_Inf := fun s a ha => (is_lub_Sup (LowerBounds s)).1 ha }

/-- Any `complete_semilattice_Sup` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Sup`.
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type _) [CompleteSemilatticeSup α] : CompleteLattice α :=
  completeLatticeOfSup α fun s => is_lub_Sup s

-- ././Mathport/Syntax/Translate/Basic.lean:1278:11: unsupported: advanced extends in structure
/-- A complete linear order is a linear order whose lattice structure is complete. -/
class CompleteLinearOrder (α : Type _) extends CompleteLattice α,
  "././Mathport/Syntax/Translate/Basic.lean:1278:11: unsupported: advanced extends in structure"

namespace OrderDual

variable (α)

instance [CompleteLattice α] : CompleteLattice (OrderDual α) :=
  { OrderDual.lattice α, OrderDual.hasSupₓ α, OrderDual.hasInfₓ α, OrderDual.boundedOrder α with
    le_Sup := @CompleteLattice.Inf_le α _, Sup_le := @CompleteLattice.le_Inf α _, Inf_le := @CompleteLattice.le_Sup α _,
    le_Inf := @CompleteLattice.Sup_le α _ }

instance [CompleteLinearOrder α] : CompleteLinearOrder (OrderDual α) :=
  { OrderDual.completeLattice α, OrderDual.linearOrder α with }

end OrderDual

section

variable [CompleteLattice α] {s t : Set α} {a b : α}

theorem Inf_le_Sup (hs : s.Nonempty) : inf s ≤ sup s :=
  is_glb_le_is_lub (is_glb_Inf s) (is_lub_Sup s) hs

theorem Sup_union {s t : Set α} : sup (s ∪ t) = sup s⊔sup t :=
  ((is_lub_Sup s).union (is_lub_Sup t)).Sup_eq

theorem Sup_inter_le {s t : Set α} : sup (s ∩ t) ≤ sup s⊓sup t :=
  Sup_le fun b hb => le_inf (le_Sup hb.1) (le_Sup hb.2)

/-
  Sup_le (λ a ⟨a_s, a_t⟩, le_inf (le_Sup a_s) (le_Sup a_t))
-/
theorem Inf_union {s t : Set α} : inf (s ∪ t) = inf s⊓inf t :=
  ((is_glb_Inf s).union (is_glb_Inf t)).Inf_eq

theorem le_Inf_inter {s t : Set α} : inf s⊔inf t ≤ inf (s ∩ t) :=
  @Sup_inter_le (OrderDual α) _ _ _

@[simp]
theorem Sup_empty : sup ∅ = (⊥ : α) :=
  (@is_lub_empty α _ _).Sup_eq

@[simp]
theorem Inf_empty : inf ∅ = (⊤ : α) :=
  (@is_glb_empty α _ _).Inf_eq

@[simp]
theorem Sup_univ : sup Univ = (⊤ : α) :=
  (@is_lub_univ α _ _).Sup_eq

@[simp]
theorem Inf_univ : inf Univ = (⊥ : α) :=
  (@is_glb_univ α _ _).Inf_eq

-- TODO(Jeremy): get this automatically
@[simp]
theorem Sup_insert {a : α} {s : Set α} : sup (insert a s) = a⊔sup s :=
  ((is_lub_Sup s).insert a).Sup_eq

@[simp]
theorem Inf_insert {a : α} {s : Set α} : inf (insert a s) = a⊓inf s :=
  ((is_glb_Inf s).insert a).Inf_eq

theorem Sup_le_Sup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : sup s ≤ sup t :=
  le_transₓ (Sup_le_Sup h) (le_of_eqₓ (trans Sup_insert bot_sup_eq))

theorem Inf_le_Inf_of_subset_insert_top (h : s ⊆ insert ⊤ t) : inf t ≤ inf s :=
  le_transₓ (le_of_eqₓ (trans top_inf_eq.symm Inf_insert.symm)) (Inf_le_Inf h)

theorem Sup_pair {a b : α} : sup {a, b} = a⊔b :=
  (@is_lub_pair α _ a b).Sup_eq

theorem Inf_pair {a b : α} : inf {a, b} = a⊓b :=
  (@is_glb_pair α _ a b).Inf_eq

@[simp]
theorem Inf_eq_top : inf s = ⊤ ↔ ∀, ∀ a ∈ s, ∀, a = ⊤ :=
  Iff.intro (fun h a ha => top_unique <| h ▸ Inf_le ha) fun h => top_unique <| le_Inf fun a ha => top_le_iff.2 <| h a ha

theorem eq_singleton_top_of_Inf_eq_top_of_nonempty {s : Set α} (h_inf : inf s = ⊤) (hne : s.Nonempty) : s = {⊤} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [Inf_eq_top] at h_inf
  exact ⟨hne, h_inf⟩

@[simp]
theorem Sup_eq_bot : sup s = ⊥ ↔ ∀, ∀ a ∈ s, ∀, a = ⊥ :=
  @Inf_eq_top (OrderDual α) _ _

theorem eq_singleton_bot_of_Sup_eq_bot_of_nonempty {s : Set α} (h_sup : sup s = ⊥) (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [Sup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `cSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem Sup_eq_of_forall_le_of_forall_lt_exists_gt (_ : ∀, ∀ a ∈ s, ∀, a ≤ b) (H : ∀ w, w < b → ∃ a ∈ s, w < a) :
    sup s = b :=
  have h : sup s < b ∨ sup s = b := lt_or_eq_of_leₓ (Sup_le ‹∀, ∀ a ∈ s, ∀, a ≤ b›)
  have : ¬sup s < b := fun hb =>
    let ⟨a, ha, ha'⟩ := H (sup s) hb
    -- a ∈ s, Sup s < a
    have : sup s < sup s := lt_of_lt_of_leₓ ha' (le_Sup ha)
    show False from lt_irreflₓ _ this
  show sup s = b from Or.resolve_left h this

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `cInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem Inf_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀, ∀ a ∈ s, ∀, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → inf s = b :=
  @Sup_eq_of_forall_le_of_forall_lt_exists_gt (OrderDual α) _ _ ‹_›

end

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s t : Set α} {a b : α}

theorem Inf_lt_iff : inf s < b ↔ ∃ a ∈ s, a < b :=
  is_glb_lt_iff <| is_glb_Inf s

theorem lt_Sup_iff : b < sup s ↔ ∃ a ∈ s, b < a :=
  lt_is_lub_iff <| is_lub_Sup s

theorem Sup_eq_top : sup s = ⊤ ↔ ∀, ∀ b < ⊤, ∀, ∃ a ∈ s, b < a :=
  Iff.intro
    (fun b hb => by
      rwa [← h, lt_Sup_iff] at hb)
    fun h =>
    top_unique <|
      le_of_not_gtₓ fun h' =>
        let ⟨a, ha, h⟩ := h _ h'
        lt_irreflₓ a <| lt_of_le_of_ltₓ (le_Sup ha) h

theorem Inf_eq_bot : inf s = ⊥ ↔ ∀, ∀ b > ⊥, ∀, ∃ a ∈ s, a < b :=
  @Sup_eq_top (OrderDual α) _ _

theorem lt_supr_iff {f : ι → α} : a < supr f ↔ ∃ i, a < f i :=
  lt_Sup_iff.trans exists_range_iff

theorem infi_lt_iff {f : ι → α} : infi f < a ↔ ∃ i, f i < a :=
  Inf_lt_iff.trans exists_range_iff

end CompleteLinearOrder

/-
### supr & infi
-/
section HasSupₓ

variable [HasSupₓ α] {f g : ι → α}

theorem Sup_range : sup (Range f) = supr f :=
  rfl

theorem Sup_eq_supr' (s : Set α) : sup s = ⨆ a : s, a := by
  rw [supr, Subtype.range_coe]

theorem supr_congr (h : ∀ i, f i = g i) : (⨆ i, f i) = ⨆ i, g i :=
  congr_argₓ _ <| funext h

theorem Function.Surjective.supr_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) : (⨆ x, g (f x)) = ⨆ y, g y := by
  simp only [supr, hf.range_comp]

protected theorem Function.Surjective.supr_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y := by
  convert h1.supr_comp g
  exact (funext h2).symm

@[congr]
theorem supr_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q) (f : ∀ x, f₁ (pq.mpr x) = f₂ x) :
    supr f₁ = supr f₂ := by
  obtain rfl := propext pq
  congr with x
  apply f

theorem supr_range' (g : β → α) (f : ι → β) : (⨆ b : Range f, g b) = ⨆ i, g (f i) := by
  rw [supr, supr, ← image_eq_range, ← range_comp]

theorem Sup_image' {s : Set β} {f : β → α} : sup (f '' s) = ⨆ a : s, f a := by
  rw [supr, image_eq_range]

end HasSupₓ

section HasInfₓ

variable [HasInfₓ α] {f g : ι → α}

theorem Inf_range : inf (Range f) = infi f :=
  rfl

theorem Inf_eq_infi' (s : Set α) : inf s = ⨅ a : s, a :=
  @Sup_eq_supr' (OrderDual α) _ _

theorem infi_congr (h : ∀ i, f i = g i) : (⨅ i, f i) = ⨅ i, g i :=
  congr_argₓ _ <| funext h

theorem Function.Surjective.infi_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) : (⨅ x, g (f x)) = ⨅ y, g y :=
  @Function.Surjective.supr_comp (OrderDual α) _ _ _ f hf g

theorem Function.Surjective.infi_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h) (h2 : ∀ x, g (h x) = f x) :
    (⨅ x, f x) = ⨅ y, g y :=
  @Function.Surjective.supr_congr (OrderDual α) _ _ _ _ _ h h1 h2

@[congr]
theorem infi_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q) (f : ∀ x, f₁ (pq.mpr x) = f₂ x) :
    infi f₁ = infi f₂ :=
  @supr_congr_Prop (OrderDual α) _ p q f₁ f₂ pq f

theorem infi_range' (g : β → α) (f : ι → β) : (⨅ b : Range f, g b) = ⨅ i, g (f i) :=
  @supr_range' (OrderDual α) _ _ _ _ _

theorem Inf_image' {s : Set β} {f : β → α} : inf (f '' s) = ⨅ a : s, f a :=
  @Sup_image' (OrderDual α) _ _ _ _

end HasInfₓ

section

variable [CompleteLattice α] {f g s t : ι → α} {a b : α}

-- TODO: this declaration gives error when starting smt state
--@[ematch]
theorem le_supr (f : ι → α) (i : ι) : f i ≤ supr f :=
  le_Sup ⟨i, rfl⟩

theorem infi_le (f : ι → α) (i : ι) : infi f ≤ f i :=
  Inf_le ⟨i, rfl⟩

@[ematch]
theorem le_supr' (f : ι → α) (i : ι) : f i ≤ supr f :=
  le_Sup ⟨i, rfl⟩

@[ematch]
theorem infi_le' (f : ι → α) (i : ι) : infi f ≤ f i :=
  Inf_le ⟨i, rfl⟩

/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] lemma le_supr' (f : ι → α) (i : ι) : (: f i :) ≤ (: supr f :) :=
le_Sup ⟨i, rfl⟩
-/
theorem is_lub_supr : IsLub (Range f) (⨆ j, f j) :=
  is_lub_Sup _

theorem is_glb_infi : IsGlb (Range f) (⨅ j, f j) :=
  is_glb_Inf _

theorem IsLub.supr_eq (h : IsLub (Range f) a) : (⨆ j, f j) = a :=
  h.Sup_eq

theorem IsGlb.infi_eq (h : IsGlb (Range f) a) : (⨅ j, f j) = a :=
  h.Inf_eq

theorem le_supr_of_le (i : ι) (h : a ≤ f i) : a ≤ supr f :=
  h.trans <| le_supr _ i

theorem infi_le_of_le (i : ι) (h : f i ≤ a) : infi f ≤ a :=
  (infi_le _ i).trans h

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem le_supr₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_supr_of_le i <| le_supr (f i) j

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem infi₂_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) : (⨅ (i) (j), f i j) ≤ f i j :=
  infi_le_of_le i <| infi_le (f i) j

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem le_supr₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) : a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_supr₂ i j

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem infi₂_le_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) : (⨅ (i) (j), f i j) ≤ a :=
  (infi₂_le i j).trans h

theorem supr_le (h : ∀ i, f i ≤ a) : supr f ≤ a :=
  Sup_le fun b ⟨i, Eq⟩ => Eq ▸ h i

theorem le_infi (h : ∀ i, a ≤ f i) : a ≤ infi f :=
  le_Inf fun b ⟨i, Eq⟩ => Eq ▸ h i

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem supr₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : (⨆ (i) (j), f i j) ≤ a :=
  supr_le fun i => supr_le <| h i

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem le_infi₂ {f : ∀ i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ (i) (j), f i j :=
  le_infi fun i => le_infi <| h i

theorem supr₂_le_supr (κ : ι → Sort _) (f : ι → α) : (⨆ (i) (j : κ i), f i) ≤ ⨆ i, f i :=
  supr₂_le fun i j => le_supr f i

theorem infi_le_infi₂ (κ : ι → Sort _) (f : ι → α) : (⨅ i, f i) ≤ ⨅ (i) (j : κ i), f i :=
  le_infi₂ fun i j => infi_le f i

theorem supr_mono (h : ∀ i, f i ≤ g i) : supr f ≤ supr g :=
  supr_le fun i => le_supr_of_le i <| h i

theorem infi_mono (h : ∀ i, f i ≤ g i) : infi f ≤ infi g :=
  le_infi fun i => infi_le_of_le i <| h i

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem supr₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) : (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  supr_mono fun i => supr_mono <| h i

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem infi₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) : (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  infi_mono fun i => infi_mono <| h i

theorem supr_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : supr f ≤ supr g :=
  supr_le fun i => Exists.elim (h i) le_supr_of_le

theorem infi_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : infi f ≤ infi g :=
  le_infi fun i' => Exists.elim (h i') infi_le_of_le

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem supr₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  supr₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_supr₂_of_le i' j' h

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem infi₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  le_infi₂ fun i j =>
    let ⟨i', j', h⟩ := h i j
    infi₂_le_of_le i' j' h

theorem supr_const_mono (h : ι → ι') : (⨆ i : ι, a) ≤ ⨆ j : ι', a :=
  supr_le <| le_supr _ ∘ h

theorem infi_const_mono (h : ι' → ι) : (⨅ i : ι, a) ≤ ⨅ j : ι', a :=
  le_infi <| infi_le _ ∘ h

theorem bsupr_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) : (⨆ (i) (h : p i), f i) ≤ ⨆ (i) (h : q i), f i :=
  supr_mono fun i => supr_const_mono (hpq i)

theorem binfi_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) : (⨅ (i) (h : q i), f i) ≤ ⨅ (i) (h : p i), f i :=
  infi_mono fun i => infi_const_mono (hpq i)

@[simp]
theorem supr_le_iff : supr f ≤ a ↔ ∀ i, f i ≤ a :=
  (is_lub_le_iff is_lub_supr).trans forall_range_iff

@[simp]
theorem le_infi_iff : a ≤ infi f ↔ ∀ i, a ≤ f i :=
  (le_is_glb_iff is_glb_infi).trans forall_range_iff

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem supr₂_le_iff {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [supr_le_iff]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem le_infi₂_iff {f : ∀ i, κ i → α} : (a ≤ ⨅ (i) (j), f i j) ↔ ∀ i j, a ≤ f i j := by
  simp_rw [le_infi_iff]

theorem supr_lt_iff : supr f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
  ⟨fun h => ⟨supr f, h, le_supr f⟩, fun ⟨b, h, hb⟩ => (supr_le hb).trans_lt h⟩

theorem lt_infi_iff : a < infi f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
  ⟨fun h => ⟨infi f, h, infi_le f⟩, fun ⟨b, h, hb⟩ => h.trans_le <| le_infi hb⟩

theorem Sup_eq_supr {s : Set α} : sup s = ⨆ a ∈ s, a :=
  le_antisymmₓ (Sup_le le_supr₂) (supr₂_le fun b => le_Sup)

theorem Inf_eq_infi {s : Set α} : inf s = ⨅ a ∈ s, a :=
  @Sup_eq_supr (OrderDual α) _ _

theorem Sup_sUnion (s : Set (Set α)) : sup (⋃₀s) = ⨆ t ∈ s, sup t := by
  apply le_antisymmₓ
  · apply Sup_le fun b hb => _
    rcases hb with ⟨t, ts, bt⟩
    apply le_transₓ _ (le_supr _ t)
    exact le_transₓ (le_Sup bt) (le_supr _ ts)
    
  · apply supr_le fun t => _
    exact supr_le fun ts => Sup_le_Sup fun x xt => ⟨t, ts, xt⟩
    

theorem Inf_sUnion (s : Set (Set α)) : inf (⋃₀s) = ⨅ t ∈ s, inf t :=
  @Sup_sUnion (OrderDual α) _ _

theorem Monotone.le_map_supr [CompleteLattice β] {f : α → β} (hf : Monotone f) : (⨆ i, f (s i)) ≤ f (supr s) :=
  supr_le fun i => hf <| le_supr _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem Monotone.le_map_supr₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨆ (i) (j), s i j) :=
  calc
    (⨆ (i) (j), f (s i j)) ≤ ⨆ i, f (⨆ j, s i j) := supr_mono fun i => hf.le_map_supr
    _ ≤ f (⨆ (i) (j), s i j) := hf.le_map_supr
    

theorem Monotone.le_map_Sup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    (⨆ a ∈ s, f a) ≤ f (sup s) := by
  rw [Sup_eq_supr] <;> exact hf.le_map_supr₂ _

theorem Antitone.le_map_infi [CompleteLattice β] {f : α → β} (hf : Antitone f) : (⨆ i, f (s i)) ≤ f (infi s) :=
  hf.dual_left.le_map_supr

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem Antitone.le_map_infi₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_supr₂ _

theorem Antitone.le_map_Inf [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    (⨆ a ∈ s, f a) ≤ f (inf s) :=
  hf.dual_left.le_map_Sup

theorem OrderIso.map_supr [CompleteLattice β] (f : α ≃o β) (x : ι → α) : f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <|
    f.Surjective.forall.2 fun x => by
      simp only [f.le_iff_le, supr_le_iff]

theorem OrderIso.map_Sup [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sup s) = ⨆ a ∈ s, f a := by
  simp only [Sup_eq_supr, OrderIso.map_supr]

theorem supr_comp_le {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨆ x, f (g x)) ≤ ⨆ y, f y :=
  supr_mono' fun x => ⟨_, le_rfl⟩

theorem Monotone.supr_comp_eq [Preorderₓ β] {f : β → α} (hf : Monotone f) {s : ι → β} (hs : ∀ x, ∃ i, x ≤ s i) :
    (⨆ x, f (s x)) = ⨆ y, f y :=
  le_antisymmₓ (supr_comp_le _ _) (supr_mono' fun x => (hs x).imp fun i hi => hf hi)

theorem Monotone.map_infi_le [CompleteLattice β] {f : α → β} (hf : Monotone f) : f (infi s) ≤ ⨅ i, f (s i) :=
  le_infi fun i => hf <| infi_le _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem Monotone.map_infi₂_le [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    f (⨅ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_supr₂ _

theorem Monotone.map_Inf_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) : f (inf s) ≤ ⨅ a ∈ s, f a :=
  by
  rw [Inf_eq_infi] <;> exact hf.map_infi₂_le _

theorem Antitone.map_supr_le [CompleteLattice β] {f : α → β} (hf : Antitone f) : f (supr s) ≤ ⨅ i, f (s i) :=
  hf.dual_left.map_infi_le

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem Antitone.map_supr₂_le [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    f (⨆ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual_left.map_infi₂_le _

theorem Antitone.map_Sup_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) : f (sup s) ≤ ⨅ a ∈ s, f a :=
  hf.dual_left.map_Inf_le

theorem OrderIso.map_infi [CompleteLattice β] (f : α ≃o β) (x : ι → α) : f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_supr f.dual _

theorem OrderIso.map_Inf [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (inf s) = ⨅ a ∈ s, f a :=
  OrderIso.map_Sup f.dual _

theorem le_infi_comp {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨅ y, f y) ≤ ⨅ x, f (g x) :=
  infi_mono' fun x => ⟨_, le_rfl⟩

theorem Monotone.infi_comp_eq [Preorderₓ β] {f : β → α} (hf : Monotone f) {s : ι → β} (hs : ∀ x, ∃ i, s i ≤ x) :
    (⨅ x, f (s x)) = ⨅ y, f y :=
  le_antisymmₓ (infi_mono' fun x => (hs x).imp fun i hi => hf hi) (le_infi_comp _ _)

theorem supr_const_le {x : α} : (⨆ h : ι, x) ≤ x :=
  supr_le fun _ => le_rfl

theorem le_infi_const {x : α} : x ≤ ⨅ h : ι, x :=
  le_infi fun _ => le_rfl

-- We will generalize this to conditionally complete lattices in `cinfi_const`.
theorem infi_const [Nonempty ι] {a : α} : (⨅ b : ι, a) = a := by
  rw [infi, range_const, Inf_singleton]

-- We will generalize this to conditionally complete lattices in `csupr_const`.
theorem supr_const [Nonempty ι] {a : α} : (⨆ b : ι, a) = a :=
  @infi_const (OrderDual α) _ _ _ _

@[simp]
theorem infi_top : (⨅ i : ι, ⊤ : α) = ⊤ :=
  top_unique <| le_infi fun i => le_rfl

@[simp]
theorem supr_bot : (⨆ i : ι, ⊥ : α) = ⊥ :=
  @infi_top (OrderDual α) _ _

@[simp]
theorem supr_eq_bot : supr s = ⊥ ↔ ∀ i, s i = ⊥ :=
  Sup_eq_bot.trans forall_range_iff

@[simp]
theorem infi_eq_top : infi s = ⊤ ↔ ∀ i, s i = ⊤ :=
  Inf_eq_top.trans forall_range_iff

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem supr₂_eq_bot {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp_rw [supr_eq_bot]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
@[simp]
theorem infi₂_eq_top {f : ∀ i, κ i → α} : (⨅ (i) (j), f i j) = ⊤ ↔ ∀ i j, f i j = ⊤ := by
  simp_rw [infi_eq_top]

@[simp]
theorem supr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  le_antisymmₓ (supr_le fun h => le_rfl) (le_supr _ _)

@[simp]
theorem infi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  le_antisymmₓ (infi_le _ _) (le_infi fun h => le_rfl)

@[simp]
theorem supr_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨆ h : p, f h) = ⊥ :=
  le_antisymmₓ (supr_le fun h => (hp h).elim) bot_le

@[simp]
theorem infi_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨅ h : p, f h) = ⊤ :=
  le_antisymmₓ le_top <| le_infi fun h => (hp h).elim

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `csupr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem supr_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b) (h₂ : ∀ w, w < b → ∃ i, w < f i) :
    (⨆ i : ι, f i) = b :=
  Sup_eq_of_forall_le_of_forall_lt_exists_gt (forall_range_iff.mpr h₁) fun w hw => exists_range_iff.mpr <| h₂ w hw

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `cinfi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem infi_eq_of_forall_ge_of_forall_gt_exists_lt {f : ι → α} (h₁ : ∀ i, b ≤ f i) (h₂ : ∀ w, b < w → ∃ i, f i < w) :
    (⨅ i : ι, f i) = b :=
  @supr_eq_of_forall_le_of_forall_lt_exists_gt (OrderDual α) _ _ _ ‹_› ‹_› ‹_›

theorem supr_eq_dif {p : Prop} [Decidable p] (a : p → α) : (⨆ h : p, a h) = if h : p then a h else ⊥ := by
  by_cases' p <;> simp [h]

theorem supr_eq_if {p : Prop} [Decidable p] (a : α) : (⨆ h : p, a) = if p then a else ⊥ :=
  supr_eq_dif fun _ => a

theorem infi_eq_dif {p : Prop} [Decidable p] (a : p → α) : (⨅ h : p, a h) = if h : p then a h else ⊤ :=
  @supr_eq_dif (OrderDual α) _ _ _ _

theorem infi_eq_if {p : Prop} [Decidable p] (a : α) : (⨅ h : p, a) = if p then a else ⊤ :=
  infi_eq_dif fun _ => a

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (j i)
-- TODO: should this be @[simp]?
theorem supr_comm {f : ι → ι' → α} : (⨆ (i) (j), f i j) = ⨆ (j) (i), f i j :=
  le_antisymmₓ (supr_le fun i => supr_mono fun j => le_supr _ i) (supr_le fun j => supr_mono fun i => le_supr _ _)

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (j i)
-- TODO: should this be @[simp]?
theorem infi_comm {f : ι → ι' → α} : (⨅ (i) (j), f i j) = ⨅ (j) (i), f i j :=
  @supr_comm (OrderDual α) _ _ _ _

/- TODO: this is strange. In the proof below, we get exactly the desired
   among the equalities, but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/
@[simp]
theorem infi_infi_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨅ x, ⨅ h : x = b, f x h) = f b rfl :=
  le_antisymmₓ (infi₂_le _ rfl)
    (le_infi fun b' =>
      le_infi fun eq =>
        match b', Eq with
        | _, rfl => le_rfl)

@[simp]
theorem infi_infi_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨅ x, ⨅ h : b = x, f x h) = f b rfl :=
  le_antisymmₓ (infi₂_le _ rfl)
    (le_infi₂ fun b' eq =>
      match b', Eq with
      | _, rfl => le_rfl)

@[simp]
theorem supr_supr_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨆ x, ⨆ h : x = b, f x h) = f b rfl :=
  @infi_infi_eq_left (OrderDual α) _ _ _ _

@[simp]
theorem supr_supr_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨆ x, ⨆ h : b = x, f x h) = f b rfl :=
  @infi_infi_eq_right (OrderDual α) _ _ _ _

attribute [ematch] le_reflₓ

theorem infi_subtype {p : ι → Prop} {f : Subtype p → α} : (⨅ x, f x) = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymmₓ (le_infi₂ fun i h => infi_le _ _) (le_infi fun ⟨i, h⟩ => infi₂_le _ _)

theorem infi_subtype' {p : ι → Prop} {f : ∀ i, p i → α} : (⨅ (i) (h : p i), f i h) = ⨅ x : Subtype p, f x x.property :=
  (@infi_subtype _ _ _ p fun x => f x.val x.property).symm

theorem infi_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨅ i : s, f i) = ⨅ (t : ι) (H : t ∈ s), f t :=
  infi_subtype

theorem infi_inf_eq {f g : ι → α} : (⨅ x, f x⊓g x) = (⨅ x, f x)⊓⨅ x, g x :=
  le_antisymmₓ (le_inf (infi_mono fun i => inf_le_left) <| infi_mono fun i => inf_le_right)
    (le_infi fun i => inf_le_inf (infi_le _ _) <| infi_le _ _)

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/
theorem infi_inf [h : Nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x)⊓a = ⨅ x, f x⊓a := by
  rw [infi_inf_eq, infi_const]

theorem inf_infi [Nonempty ι] {f : ι → α} {a : α} : (a⊓⨅ x, f x) = ⨅ x, a⊓f x := by
  rw [inf_comm, infi_inf] <;> simp [inf_comm]

theorem binfi_inf {p : ι → Prop} {f : ∀ i hi : p i, α} {a : α} (h : ∃ i, p i) :
    (⨅ (i) (h : p i), f i h)⊓a = ⨅ (i) (h : p i), f i h⊓a := by
  have : Nonempty { i // p i } :=
      let ⟨i, hi⟩ := h
      ⟨⟨i, hi⟩⟩ <;>
    rw [infi_subtype', infi_subtype', infi_inf]

theorem inf_binfi {p : ι → Prop} {f : ∀ i hi : p i, α} {a : α} (h : ∃ i, p i) :
    (a⊓⨅ (i) (h : p i), f i h) = ⨅ (i) (h : p i), a⊓f i h := by
  simpa only [inf_comm] using binfi_inf h

theorem supr_sup_eq {f g : ι → α} : (⨆ x, f x⊔g x) = (⨆ x, f x)⊔⨆ x, g x :=
  @infi_inf_eq (OrderDual α) ι _ _ _

theorem supr_sup [h : Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x)⊔a = ⨆ x, f x⊔a :=
  @infi_inf (OrderDual α) _ _ _ _ _

theorem sup_supr [Nonempty ι] {f : ι → α} {a : α} : (a⊔⨆ x, f x) = ⨆ x, a⊔f x :=
  @inf_infi (OrderDual α) _ _ _ _ _

/-! ### `supr` and `infi` under `Prop` -/


@[simp]
theorem infi_false {s : False → α} : infi s = ⊤ :=
  le_antisymmₓ le_top (le_infi fun i => False.elim i)

@[simp]
theorem supr_false {s : False → α} : supr s = ⊥ :=
  le_antisymmₓ (supr_le fun i => False.elim i) bot_le

theorem supr_true {s : True → α} : supr s = s trivialₓ :=
  supr_pos trivialₓ

theorem infi_true {s : True → α} : infi s = s trivialₓ :=
  infi_pos trivialₓ

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i h)
@[simp]
theorem infi_exists {p : ι → Prop} {f : Exists p → α} : (⨅ x, f x) = ⨅ (i) (h), f ⟨i, h⟩ :=
  le_antisymmₓ (le_infi₂ fun i h => infi_le _ _) (le_infi fun ⟨i, h⟩ => infi₂_le _ _)

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i h)
@[simp]
theorem supr_exists {p : ι → Prop} {f : Exists p → α} : (⨆ x, f x) = ⨆ (i) (h), f ⟨i, h⟩ :=
  @infi_exists (OrderDual α) _ _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (h₁ h₂)
theorem infi_and {p q : Prop} {s : p ∧ q → α} : infi s = ⨅ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymmₓ (le_infi₂ fun i j => infi_le _ _) (le_infi fun ⟨i, h⟩ => infi₂_le _ _)

/-- The symmetric case of `infi_and`, useful for rewriting into a infimum over a conjunction -/
theorem infi_and' {p q : Prop} {s : p → q → α} : (⨅ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨅ h : p ∧ q, s h.1 h.2 := by
  symm
  exact infi_and

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (h₁ h₂)
theorem supr_and {p q : Prop} {s : p ∧ q → α} : supr s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  @infi_and (OrderDual α) _ _ _ _

/-- The symmetric case of `supr_and`, useful for rewriting into a supremum over a conjunction -/
theorem supr_and' {p q : Prop} {s : p → q → α} : (⨆ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨆ h : p ∧ q, s h.1 h.2 := by
  symm
  exact supr_and

theorem infi_or {p q : Prop} {s : p ∨ q → α} : infi s = (⨅ h : p, s (Or.inl h))⊓⨅ h : q, s (Or.inr h) :=
  le_antisymmₓ (le_inf (le_infi_comp _ _) <| le_infi_comp _ _)
    (le_infi fun i =>
      match i with
      | Or.inl i => inf_le_of_left_le <| infi_le _ _
      | Or.inr j => inf_le_of_right_le <| infi_le _ _)

theorem supr_or {p q : Prop} {s : p ∨ q → α} : (⨆ x, s x) = (⨆ i, s (Or.inl i))⊔⨆ j, s (Or.inr j) :=
  @infi_or (OrderDual α) _ _ _ _

section

variable (p : ι → Prop) [DecidablePred p]

theorem supr_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨆ i, if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h)⊔⨆ (i) (h : ¬p i), g i h := by
  rw [← supr_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]

theorem supr_ite (f g : ι → α) : (⨆ i, if p i then f i else g i) = (⨆ (i) (h : p i), f i)⊔⨆ (i) (h : ¬p i), g i :=
  supr_dite _ _ _

theorem infi_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨅ i, if h : p i then f i h else g i h) = (⨅ (i) (h : p i), f i h)⊓⨅ (i) (h : ¬p i), g i h :=
  supr_dite p (show ∀ i, p i → OrderDual α from f) g

theorem infi_ite (f g : ι → α) : (⨅ i, if p i then f i else g i) = (⨅ (i) (h : p i), f i)⊓⨅ (i) (h : ¬p i), g i :=
  infi_dite _ _ _

end

theorem infi_range {g : β → α} {f : ι → β} : (⨅ b ∈ Range f, g b) = ⨅ i, g (f i) := by
  rw [← infi_subtype'', infi_range']

theorem supr_range {g : β → α} {f : ι → β} : (⨆ b ∈ Range f, g b) = ⨆ i, g (f i) :=
  @infi_range (OrderDual α) _ _ _ _ _

theorem Inf_image {s : Set β} {f : β → α} : inf (f '' s) = ⨅ a ∈ s, f a := by
  rw [← infi_subtype'', Inf_image']

theorem Sup_image {s : Set β} {f : β → α} : sup (f '' s) = ⨆ a ∈ s, f a :=
  @Inf_image (OrderDual α) _ _ _ _

/-
### supr and infi under set constructions
-/
theorem infi_emptyset {f : β → α} : (⨅ x ∈ (∅ : Set β), f x) = ⊤ := by
  simp

theorem supr_emptyset {f : β → α} : (⨆ x ∈ (∅ : Set β), f x) = ⊥ := by
  simp

theorem infi_univ {f : β → α} : (⨅ x ∈ (Univ : Set β), f x) = ⨅ x, f x := by
  simp

theorem supr_univ {f : β → α} : (⨆ x ∈ (Univ : Set β), f x) = ⨆ x, f x := by
  simp

theorem infi_union {f : β → α} {s t : Set β} : (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x)⊓⨅ x ∈ t, f x := by
  simp only [← infi_inf_eq, infi_or]

theorem infi_split (f : β → α) (p : β → Prop) : (⨅ i, f i) = (⨅ (i) (h : p i), f i)⊓⨅ (i) (h : ¬p i), f i := by
  simpa [Classical.em] using @infi_union _ _ _ f { i | p i } { i | ¬p i }

theorem infi_split_single (f : β → α) (i₀ : β) : (⨅ i, f i) = f i₀⊓⨅ (i) (h : i ≠ i₀), f i := by
  convert infi_split _ _ <;> simp

theorem infi_le_infi_of_subset {f : β → α} {s t : Set β} (h : s ⊆ t) : (⨅ x ∈ t, f x) ≤ ⨅ x ∈ s, f x := by
  rw [(union_eq_self_of_subset_left h).symm, infi_union] <;> exact inf_le_left

theorem supr_union {f : β → α} {s t : Set β} : (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x)⊔⨆ x ∈ t, f x :=
  @infi_union (OrderDual α) _ _ _ _ _

theorem supr_split (f : β → α) (p : β → Prop) : (⨆ i, f i) = (⨆ (i) (h : p i), f i)⊔⨆ (i) (h : ¬p i), f i :=
  @infi_split (OrderDual α) _ _ _ _

theorem supr_split_single (f : β → α) (i₀ : β) : (⨆ i, f i) = f i₀⊔⨆ (i) (h : i ≠ i₀), f i :=
  @infi_split_single (OrderDual α) _ _ _ _

theorem supr_le_supr_of_subset {f : β → α} {s t : Set β} (h : s ⊆ t) : (⨆ x ∈ s, f x) ≤ ⨆ x ∈ t, f x :=
  @infi_le_infi_of_subset (OrderDual α) _ _ _ _ _ h

theorem infi_insert {f : β → α} {s : Set β} {b : β} : (⨅ x ∈ insert b s, f x) = f b⊓⨅ x ∈ s, f x :=
  Eq.trans infi_union <| congr_argₓ (fun x => x⊓⨅ x ∈ s, f x) infi_infi_eq_left

theorem supr_insert {f : β → α} {s : Set β} {b : β} : (⨆ x ∈ insert b s, f x) = f b⊔⨆ x ∈ s, f x :=
  Eq.trans supr_union <| congr_argₓ (fun x => x⊔⨆ x ∈ s, f x) supr_supr_eq_left

theorem infi_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : Set β), f x) = f b := by
  simp

theorem infi_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : Set β), f x) = f a⊓f b := by
  rw [infi_insert, infi_singleton]

theorem supr_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : Set β), f x) = f b :=
  @infi_singleton (OrderDual α) _ _ _ _

theorem supr_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : Set β), f x) = f a⊔f b := by
  rw [supr_insert, supr_singleton]

theorem infi_image {γ} {f : β → γ} {g : γ → α} {t : Set β} : (⨅ c ∈ f '' t, g c) = ⨅ b ∈ t, g (f b) := by
  rw [← Inf_image, ← Inf_image, ← image_comp]

theorem supr_image {γ} {f : β → γ} {g : γ → α} {t : Set β} : (⨆ c ∈ f '' t, g c) = ⨆ b ∈ t, g (f b) :=
  @infi_image (OrderDual α) _ _ _ _ _ _

theorem supr_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) : (⨆ j, extendₓ e f ⊥ j) = ⨆ i, f i := by
  rw [supr_split _ fun j => ∃ i, e i = j]
  simp (config := { contextual := true })[extend_apply he, extend_apply', @supr_comm _ β ι]

/-!
### `supr` and `infi` under `Type`
-/


theorem supr_of_empty' {α ι} [HasSupₓ α] [IsEmpty ι] (f : ι → α) : supr f = sup (∅ : Set α) :=
  congr_argₓ sup (range_eq_empty f)

theorem supr_of_empty [IsEmpty ι] (f : ι → α) : supr f = ⊥ :=
  (supr_of_empty' f).trans Sup_empty

theorem infi_of_empty' {α ι} [HasInfₓ α] [IsEmpty ι] (f : ι → α) : infi f = inf (∅ : Set α) :=
  congr_argₓ inf (range_eq_empty f)

theorem infi_of_empty [IsEmpty ι] (f : ι → α) : infi f = ⊤ :=
  @supr_of_empty (OrderDual α) _ _ _ f

theorem supr_bool_eq {f : Bool → α} : (⨆ b : Bool, f b) = f true⊔f false := by
  rw [supr, Bool.range_eq, Sup_pair, sup_comm]

theorem infi_bool_eq {f : Bool → α} : (⨅ b : Bool, f b) = f true⊓f false :=
  @supr_bool_eq (OrderDual α) _ _

theorem sup_eq_supr (x y : α) : x⊔y = ⨆ b : Bool, cond b x y := by
  rw [supr_bool_eq, Bool.cond_tt, Bool.cond_ff]

theorem inf_eq_infi (x y : α) : x⊓y = ⨅ b : Bool, cond b x y :=
  @sup_eq_supr (OrderDual α) _ _ _

theorem is_glb_binfi {s : Set β} {f : β → α} : IsGlb (f '' s) (⨅ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, infi_subtype'] using @is_glb_infi α s _ (f ∘ coe)

theorem supr_subtype {p : ι → Prop} {f : Subtype p → α} : (⨆ x, f x) = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  @infi_subtype (OrderDual α) _ _ _ _

theorem supr_subtype' {p : ι → Prop} {f : ∀ i, p i → α} : (⨆ (i) (h : p i), f i h) = ⨆ x : Subtype p, f x x.property :=
  (@supr_subtype _ _ _ p fun x => f x.val x.property).symm

theorem supr_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨆ i : s, f i) = ⨆ (t : ι) (H : t ∈ s), f t :=
  supr_subtype

theorem is_lub_bsupr {s : Set β} {f : β → α} : IsLub (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, supr_subtype'] using @is_lub_supr α s _ (f ∘ coe)

theorem infi_sigma {p : β → Type _} {f : Sigma p → α} : (⨅ x, f x) = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  eq_of_forall_le_iff fun c => by
    simp only [le_infi_iff, Sigma.forall]

theorem supr_sigma {p : β → Type _} {f : Sigma p → α} : (⨆ x, f x) = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  @infi_sigma (OrderDual α) _ _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem infi_prod {γ : Type _} {f : β × γ → α} : (⨅ x, f x) = ⨅ (i) (j), f (i, j) :=
  eq_of_forall_le_iff fun c => by
    simp only [le_infi_iff, Prod.forall]

-- ././Mathport/Syntax/Translate/Basic.lean:745:6: warning: expanding binder group (i j)
theorem supr_prod {γ : Type _} {f : β × γ → α} : (⨆ x, f x) = ⨆ (i) (j), f (i, j) :=
  @infi_prod (OrderDual α) _ _ _ _

theorem infi_sum {γ : Type _} {f : Sum β γ → α} : (⨅ x, f x) = (⨅ i, f (Sum.inl i))⊓⨅ j, f (Sum.inr j) :=
  eq_of_forall_le_iff fun c => by
    simp only [le_inf_iff, le_infi_iff, Sum.forall]

theorem supr_sum {γ : Type _} {f : Sum β γ → α} : (⨆ x, f x) = (⨆ i, f (Sum.inl i))⊔⨆ j, f (Sum.inr j) :=
  @infi_sum (OrderDual α) _ _ _ _

theorem supr_option (f : Option β → α) : (⨆ o, f o) = f none⊔⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by
    simp only [supr_le_iff, sup_le_iff, Option.forall]

theorem infi_option (f : Option β → α) : (⨅ o, f o) = f none⊓⨅ b, f (Option.some b) :=
  @supr_option (OrderDual α) _ _ _

/-- A version of `supr_option` useful for rewriting right-to-left. -/
theorem supr_option_elim (a : α) (f : β → α) : (⨆ o : Option β, o.elim a f) = a⊔⨆ b, f b := by
  simp [supr_option]

/-- A version of `infi_option` useful for rewriting right-to-left. -/
theorem infi_option_elim (a : α) (f : β → α) : (⨅ o : Option β, o.elim a f) = a⊓⨅ b, f b :=
  @supr_option_elim (OrderDual α) _ _ _ _

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
theorem supr_ne_bot_subtype (f : ι → α) : (⨆ i : { i // f i ≠ ⊥ }, f i) = ⨆ i, f i := by
  by_cases' htriv : ∀ i, f i = ⊥
  · simp only [htriv, supr_bot]
    
  refine' le_antisymmₓ (supr_comp_le f _) (supr_mono' _)
  intro i
  by_cases' hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
    
  · exact ⟨⟨i, hi⟩, rfl.le⟩
    

/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
theorem infi_ne_top_subtype (f : ι → α) : (⨅ i : { i // f i ≠ ⊤ }, f i) = ⨅ i, f i :=
  @supr_ne_bot_subtype (OrderDual α) ι _ f

/-!
### `supr` and `infi` under `ℕ`
-/


theorem supr_ge_eq_supr_nat_add {u : ℕ → α} (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) := by
  apply le_antisymmₓ <;> simp only [supr_le_iff]
  · exact fun i hi =>
      le_Sup
        ⟨i - n, by
          dsimp' only
          rw [tsub_add_cancel_of_le hi]⟩
    
  · exact fun i => le_Sup ⟨i + n, supr_pos (Nat.le_add_leftₓ _ _)⟩
    

theorem infi_ge_eq_infi_nat_add {u : ℕ → α} (n : ℕ) : (⨅ i ≥ n, u i) = ⨅ i, u (i + n) :=
  @supr_ge_eq_supr_nat_add (OrderDual α) _ _ _

theorem Monotone.supr_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : (⨆ n, f (n + k)) = ⨆ n, f n :=
  le_antisymmₓ (supr_le fun i => le_supr _ (i + k)) <| supr_mono fun i => hf <| Nat.le_add_rightₓ i k

@[simp]
theorem supr_infi_ge_nat_add (f : ℕ → α) (k : ℕ) : (⨆ n, ⨅ i ≥ n, f (i + k)) = ⨆ n, ⨅ i ≥ n, f i := by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m h => binfi_mono fun i => h.trans
  rw [← Monotone.supr_nat_add hf k]
  · simp_rw [infi_ge_eq_infi_nat_add, ← Nat.add_assoc]
    

theorem sup_supr_nat_succ (u : ℕ → α) : (u 0⊔⨆ i, u (i + 1)) = ⨆ i, u i := by
  refine' eq_of_forall_ge_iff fun c => _
  simp only [sup_le_iff, supr_le_iff]
  refine' ⟨fun h => _, fun h => ⟨h _, fun i => h _⟩⟩
  rintro (_ | i)
  exacts[h.1, h.2 i]

theorem inf_infi_nat_succ (u : ℕ → α) : (u 0⊓⨅ i, u (i + 1)) = ⨅ i, u i :=
  @sup_supr_nat_succ (OrderDual α) _ u

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

theorem supr_eq_top (f : ι → α) : supr f = ⊤ ↔ ∀, ∀ b < ⊤, ∀, ∃ i, b < f i := by
  simp only [← Sup_range, Sup_eq_top, Set.exists_range_iff]

theorem infi_eq_bot (f : ι → α) : infi f = ⊥ ↔ ∀, ∀ b > ⊥, ∀, ∃ i, f i < b := by
  simp only [← Inf_range, Inf_eq_bot, Set.exists_range_iff]

end CompleteLinearOrder

/-!
### Instances
-/


instance Prop.completeLattice : CompleteLattice Prop :=
  { Prop.boundedOrder, Prop.distribLattice with sup := fun s => ∃ a ∈ s, a, le_Sup := fun s a h p => ⟨a, h, p⟩,
    Sup_le := fun s a h ⟨b, h', p⟩ => h b h' p, inf := fun s => ∀ a, a ∈ s → a, Inf_le := fun s a h p => p a h,
    le_Inf := fun s a h p b hb => h b hb p }

noncomputable instance Prop.completeLinearOrder : CompleteLinearOrder Prop :=
  { Prop.completeLattice, Prop.linearOrder with }

@[simp]
theorem Sup_Prop_eq {s : Set Prop} : sup s = ∃ p ∈ s, p :=
  rfl

@[simp]
theorem Inf_Prop_eq {s : Set Prop} : inf s = ∀, ∀ p ∈ s, ∀, p :=
  rfl

@[simp]
theorem infi_Prop_eq {p : ι → Prop} : (⨅ i, p i) = ∀ i, p i :=
  le_antisymmₓ (fun h i => h _ ⟨i, rfl⟩) fun h p ⟨i, Eq⟩ => Eq ▸ h i

@[simp]
theorem supr_Prop_eq {p : ι → Prop} : (⨆ i, p i) = ∃ i, p i :=
  le_antisymmₓ (fun ⟨q, ⟨i, (Eq : p i = q)⟩, hq⟩ => ⟨i, Eq.symm ▸ hq⟩) fun ⟨i, hi⟩ => ⟨p i, ⟨i, rfl⟩, hi⟩

instance Pi.hasSupₓ {α : Type _} {β : α → Type _} [∀ i, HasSupₓ (β i)] : HasSupₓ (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩

instance Pi.hasInfₓ {α : Type _} {β : α → Type _} [∀ i, HasInfₓ (β i)] : HasInfₓ (∀ i, β i) :=
  ⟨fun s i => ⨅ f : s, (f : ∀ i, β i) i⟩

instance Pi.completeLattice {α : Type _} {β : α → Type _} [∀ i, CompleteLattice (β i)] : CompleteLattice (∀ i, β i) :=
  { Pi.boundedOrder, Pi.lattice with sup := sup, inf := inf,
    le_Sup := fun s f hf i => le_supr (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩,
    Inf_le := fun s f hf i => infi_le (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩,
    Sup_le := fun s f hf i => supr_le fun g => hf g g.2 i, le_Inf := fun s f hf i => le_infi fun g => hf g g.2 i }

theorem Inf_apply {α : Type _} {β : α → Type _} [∀ i, HasInfₓ (β i)] {s : Set (∀ a, β a)} {a : α} :
    (inf s) a = ⨅ f : s, (f : ∀ a, β a) a :=
  rfl

@[simp]
theorem infi_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, HasInfₓ (β i)] {f : ι → ∀ a, β a} {a : α} :
    (⨅ i, f i) a = ⨅ i, f i a := by
  rw [infi, Inf_apply, infi, infi, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ← range_comp]

theorem Sup_apply {α : Type _} {β : α → Type _} [∀ i, HasSupₓ (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sup s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl

theorem unary_relation_Sup_iff {α : Type _} (s : Set (α → Prop)) {a : α} : sup s a ↔ ∃ r : α → Prop, r ∈ s ∧ r a := by
  change (∃ _, _) ↔ _
  simp [-eq_iff_iff]

theorem binary_relation_Sup_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sup s a b ↔ ∃ r : α → β → Prop, r ∈ s ∧ r a b := by
  change (∃ _, _) ↔ _
  simp [-eq_iff_iff]

@[simp]
theorem supr_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, HasSupₓ (β i)] {f : ι → ∀ a, β a} {a : α} :
    (⨆ i, f i) a = ⨆ i, f i a :=
  @infi_apply α (fun i => OrderDual (β i)) _ _ f a

section CompleteLattice

variable [Preorderₓ α] [CompleteLattice β]

theorem monotone_Sup_of_monotone {s : Set (α → β)} (m_s : ∀, ∀ f ∈ s, ∀, Monotone f) : Monotone (sup s) := fun x y h =>
  supr_mono fun f => m_s f f.2 h

theorem monotone_Inf_of_monotone {s : Set (α → β)} (m_s : ∀, ∀ f ∈ s, ∀, Monotone f) : Monotone (inf s) := fun x y h =>
  infi_mono fun f => m_s f f.2 h

end CompleteLattice

namespace Prod

variable (α β)

instance [HasInfₓ α] [HasInfₓ β] : HasInfₓ (α × β) :=
  ⟨fun s => (inf (Prod.fst '' s), inf (Prod.snd '' s))⟩

instance [HasSupₓ α] [HasSupₓ β] : HasSupₓ (α × β) :=
  ⟨fun s => (sup (Prod.fst '' s), sup (Prod.snd '' s))⟩

instance [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.hasSupₓ α β, Prod.hasInfₓ α β with
    le_Sup := fun s p hab => ⟨le_Sup <| mem_image_of_mem _ hab, le_Sup <| mem_image_of_mem _ hab⟩,
    Sup_le := fun s p h =>
      ⟨Sup_le <| ball_image_of_ball fun p hp => (h p hp).1, Sup_le <| ball_image_of_ball fun p hp => (h p hp).2⟩,
    Inf_le := fun s p hab => ⟨Inf_le <| mem_image_of_mem _ hab, Inf_le <| mem_image_of_mem _ hab⟩,
    le_Inf := fun s p h =>
      ⟨le_Inf <| ball_image_of_ball fun p hp => (h p hp).1, le_Inf <| ball_image_of_ball fun p hp => (h p hp).2⟩ }

end Prod

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/-- This is a weaker version of `sup_Inf_eq` -/
theorem sup_Inf_le_infi_sup : a⊔inf s ≤ ⨅ b ∈ s, a⊔b :=
  le_infi₂ fun i h => sup_le_sup_left (Inf_le h) _

/-- This is a weaker version of `Inf_sup_eq` -/
theorem Inf_sup_le_infi_sup : inf s⊔a ≤ ⨅ b ∈ s, b⊔a :=
  le_infi₂ fun i h => sup_le_sup_right (Inf_le h) _

/-- This is a weaker version of `inf_Sup_eq` -/
theorem supr_inf_le_inf_Sup : (⨆ b ∈ s, a⊓b) ≤ a⊓sup s :=
  supr₂_le fun i h => inf_le_inf_left _ (le_Sup h)

/-- This is a weaker version of `Sup_inf_eq` -/
theorem supr_inf_le_Sup_inf : (⨆ b ∈ s, b⊓a) ≤ sup s⊓a :=
  supr₂_le fun i h => inf_le_inf_right _ (le_Sup h)

theorem disjoint_Sup_left {a : Set α} {b : α} (d : Disjoint (sup a) b) {i} (hi : i ∈ a) : Disjoint i b :=
  (supr₂_le_iff.1 (supr_inf_le_Sup_inf.trans d) i hi : _)

theorem disjoint_Sup_right {a : Set α} {b : α} (d : Disjoint b (sup a)) {i} (hi : i ∈ a) : Disjoint b i :=
  (supr₂_le_iff.mp (supr_inf_le_inf_Sup.trans d) i hi : _)

end CompleteLattice

/-- Pullback a `complete_lattice` along an injection. -/
-- See note [reducible non-instances]
@[reducible]
protected def Function.Injective.completeLattice [HasSup α] [HasInf α] [HasSupₓ α] [HasInfₓ α] [HasTop α] [HasBot α]
    [CompleteLattice β] (f : α → β) (hf : Function.Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_Sup : ∀ s, f (sup s) = ⨆ a ∈ s, f a)
    (map_Inf : ∀ s, f (inf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α :=
  { -- we cannot use bounded_order.lift here as the `has_le` instance doesn't exist yet
        hf.Lattice
      f map_sup map_inf with
    sup := sup, le_Sup := fun s a h => (le_supr₂ a h).trans (map_Sup _).Ge,
    Sup_le := fun s a h => (map_Sup _).trans_le <| supr₂_le h, inf := inf,
    Inf_le := fun s a h => (map_Inf _).trans_le <| infi₂_le a h,
    le_Inf := fun s a h => (le_infi₂ h).trans (map_Inf _).Ge, top := ⊤,
    le_top := fun a => (@le_top β _ _ _).trans map_top.Ge, bot := ⊥, bot_le := fun a => map_bot.le.trans bot_le }

