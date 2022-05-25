/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.Connected
import Mathbin.Topology.NhdsSet

/-!
# Separation properties of topological spaces.

This file defines the predicate `separated`, and common separation axioms
(under the Kolmogorov classification).

## Main definitions

* `separated`: Two `set`s are separated if they are contained in disjoint open sets.
* `t0_space`: A T₀/Kolmogorov space is a space where, for every two points `x ≠ y`,
  there is an open set that contains one, but not the other.
* `t1_space`: A T₁/Fréchet space is a space where every singleton set is closed.
  This is equivalent to, for every pair `x ≠ y`, there existing an open set containing `x`
  but not `y` (`t1_space_iff_exists_open` shows that these conditions are equivalent.)
* `t2_space`: A T₂/Hausdorff space is a space where, for every two points `x ≠ y`,
  there is two disjoint open sets, one containing `x`, and the other `y`.
* `t2_5_space`: A T₂.₅/Urysohn space is a space where, for every two points `x ≠ y`,
  there is two open sets, one containing `x`, and the other `y`, whose closures are disjoint.
* `regular_space`: A T₃ space (sometimes referred to as regular, but authors vary on
  whether this includes T₂; `mathlib` does), is one where given any closed `C` and `x ∉ C`,
  there is disjoint open sets containing `x` and `C` respectively. In `mathlib`, T₃ implies T₂.₅.
* `normal_space`: A T₄ space (sometimes referred to as normal, but authors vary on
  whether this includes T₂; `mathlib` does), is one where given two disjoint closed sets,
  we can find two open sets that separate them. In `mathlib`, T₄ implies T₃.

## Main results

### T₀ spaces

* `is_closed.exists_closed_singleton` Given a closed set `S` in a compact T₀ space,
  there is some `x ∈ S` such that `{x}` is closed.
* `exists_open_singleton_of_open_finset` Given an open `finset` `S` in a T₀ space,
  there is some `x ∈ S` such that `{x}` is open.

### T₁ spaces

* `is_closed_map_const`: The constant map is a closed map.
* `discrete_of_t1_of_finite`: A finite T₁ space must have the discrete topology.

### T₂ spaces

* `t2_iff_nhds`: A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter.
* `t2_iff_is_closed_diagonal`: A space is T₂ iff the `diagonal` of `α` (that is, the set of all
  points of the form `(a, a) : α × α`) is closed under the product topology.
* `finset_disjoint_finset_opens_of_t2`: Any two disjoint finsets are `separated`.
* Most topological constructions preserve Hausdorffness;
  these results are part of the typeclass inference system (e.g. `embedding.t2_space`)
* `set.eq_on.closure`: If two functions are equal on some set `s`, they are equal on its closure.
* `is_compact.is_closed`: All compact sets are closed.
* `locally_compact_of_compact_nhds`: If every point has a compact neighbourhood,
  then the space is locally compact.
* `tot_sep_of_zero_dim`: If `α` has a clopen basis, it is a `totally_separated_space`.
* `loc_compact_t2_tot_disc_iff_tot_sep`: A locally compact T₂ space is totally disconnected iff
  it is totally separated.

If the space is also compact:

* `normal_of_compact_t2`: A compact T₂ space is a `normal_space`.
* `connected_components_eq_Inter_clopen`: The connected component of a point
  is the intersection of all its clopen neighbourhoods.
* `compact_t2_tot_disc_iff_tot_sep`: Being a `totally_disconnected_space`
  is equivalent to being a `totally_separated_space`.
* `connected_components.t2`: `connected_components α` is T₂ for `α` T₂ and compact.

### T₃ spaces

* `disjoint_nested_nhds`: Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and
  `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.

### Discrete spaces

* `discrete_topology_iff_nhds`: Discrete topological spaces are those whose neighbourhood
  filters are the `pure` filter (which is the principal filter at a singleton).
* `induced_bot`/`discrete_topology_induced`: The pullback of the discrete topology
  under an inclusion is the discrete topology.

## References

https://en.wikipedia.org/wiki/Separation_axiom
-/


open Set Filter TopologicalSpace

open TopologicalSpace Filter Classical

universe u v

variable {α : Type u} {β : Type v} [TopologicalSpace α]

section Separation

/-- `separated` is a predicate on pairs of sub`set`s of a topological space.  It holds if the two
sub`set`s are contained in disjoint open sets.
-/
def Separated : Set α → Set α → Prop := fun s t : Set α =>
  ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V

namespace Separated

open Separated

@[symm]
theorem symm {s t : Set α} : Separated s t → Separated t s := fun ⟨U, V, oU, oV, aU, bV, UV⟩ =>
  ⟨V, U, oV, oU, bV, aU, Disjoint.symm UV⟩

theorem comm (s t : Set α) : Separated s t ↔ Separated t s :=
  ⟨symm, symm⟩

theorem preimage [TopologicalSpace β] {f : α → β} {s t : Set β} (h : Separated s t) (hf : Continuous f) :
    Separated (f ⁻¹' s) (f ⁻¹' t) :=
  let ⟨U, V, oU, oV, sU, tV, UV⟩ := h
  ⟨f ⁻¹' U, f ⁻¹' V, oU.Preimage hf, oV.Preimage hf, preimage_mono sU, preimage_mono tV, UV.Preimage f⟩

protected theorem disjoint {s t : Set α} (h : Separated s t) : Disjoint s t :=
  let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  hd.mono hsU htV

theorem disjoint_closure_left {s t : Set α} (h : Separated s t) : Disjoint (Closure s) t :=
  let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  (hd.closure_left hV).mono (closure_mono hsU) htV

theorem disjoint_closure_right {s t : Set α} (h : Separated s t) : Disjoint s (Closure t) :=
  h.symm.disjoint_closure_left.symm

theorem empty_right (a : Set α) : Separated a ∅ :=
  ⟨_, _, is_open_univ, is_open_empty, fun a h => mem_univ a, fun a h => by
    cases h, disjoint_empty _⟩

theorem empty_left (a : Set α) : Separated ∅ a :=
  (empty_right _).symm

theorem mono {s₁ s₂ t₁ t₂ : Set α} (h : Separated s₂ t₂) (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : Separated s₁ t₁ :=
  let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  ⟨U, V, hU, hV, hs.trans hsU, ht.trans htV, hd⟩

theorem union_left {a b c : Set α} : Separated a c → Separated b c → Separated (a ∪ b) c :=
  fun ⟨U, V, oU, oV, aU, bV, UV⟩ ⟨W, X, oW, oX, aW, bX, WX⟩ =>
  ⟨U ∪ W, V ∩ X, IsOpen.union oU oW, IsOpen.inter oV oX, union_subset_union aU aW, subset_inter bV bX,
    Set.disjoint_union_left.mpr
      ⟨disjoint_of_subset_right (inter_subset_left _ _) UV, disjoint_of_subset_right (inter_subset_right _ _) WX⟩⟩

theorem union_right {a b c : Set α} (ab : Separated a b) (ac : Separated a c) : Separated a (b ∪ c) :=
  (ab.symm.union_left ac.symm).symm

end Separated

/-- A T₀ space, also known as a Kolmogorov space, is a topological space
  where for every pair `x ≠ y`, there is an open set containing one but not the other. -/
class T0Space (α : Type u) [TopologicalSpace α] : Prop where
  t0 : ∀ x y, x ≠ y → ∃ U : Set α, IsOpen U ∧ Xorₓ (x ∈ U) (y ∈ U)

theorem t0_space_def (α : Type u) [TopologicalSpace α] :
    T0Space α ↔ ∀ x y, x ≠ y → ∃ U : Set α, IsOpen U ∧ Xorₓ (x ∈ U) (y ∈ U) := by
  constructor
  apply @T0Space.t0
  apply T0Space.mk

/-- Two points are topologically indistinguishable if no open set separates them. -/
def Indistinguishable {α : Type u} [TopologicalSpace α] (x y : α) : Prop :=
  ∀ U : Set α hU : IsOpen U, x ∈ U ↔ y ∈ U

theorem indistinguishable_iff_nhds_eq {x y : α} : Indistinguishable x y ↔ 𝓝 x = 𝓝 y :=
  ⟨fun h => by
    simp (config := { contextual := true })only [nhds_def', h _], fun h U hU => by
    simp only [← hU.mem_nhds_iff, h]⟩

alias indistinguishable_iff_nhds_eq ↔ Indistinguishable.nhds_eq _

theorem t0_space_iff_distinguishable (α : Type u) [TopologicalSpace α] :
    T0Space α ↔ ∀ x y : α, x ≠ y → ¬Indistinguishable x y := by
  delta' Indistinguishable
  rw [t0_space_def]
  push_neg
  simp_rw [xor_iff_not_iff]

@[simp]
theorem nhds_eq_nhds_iff [T0Space α] {a b : α} : 𝓝 a = 𝓝 b ↔ a = b :=
  Function.Injective.eq_iff fun x y h =>
    of_not_not fun hne => (t0_space_iff_distinguishable α).mp ‹_› x y hne (indistinguishable_iff_nhds_eq.mpr h)

theorem Indistinguishable.eq [T0Space α] {x y : α} (h : Indistinguishable x y) : x = y :=
  nhds_eq_nhds_iff.mp h.nhds_eq

theorem indistinguishable_iff_closed {x y : α} : Indistinguishable x y ↔ ∀ U : Set α hU : IsClosed U, x ∈ U ↔ y ∈ U :=
  ⟨fun h U hU => not_iff_not.mp (h _ hU.1), fun h U hU => not_iff_not.mp (h _ (is_closed_compl_iff.mpr hU))⟩

theorem indistinguishable_iff_closure (x y : α) :
    Indistinguishable x y ↔ x ∈ Closure ({y} : Set α) ∧ y ∈ Closure ({x} : Set α) := by
  rw [indistinguishable_iff_closed]
  exact
    ⟨fun h =>
      ⟨(h _ is_closed_closure).mpr (subset_closure <| Set.mem_singleton y),
        (h _ is_closed_closure).mp (subset_closure <| Set.mem_singleton x)⟩,
      fun h U hU =>
      ⟨fun hx => (IsClosed.closure_subset_iff hU).mpr (set.singleton_subset_iff.mpr hx) h.2, fun hy =>
        (IsClosed.closure_subset_iff hU).mpr (set.singleton_subset_iff.mpr hy) h.1⟩⟩

theorem subtype_indistinguishable_iff {α : Type u} [TopologicalSpace α] {U : Set α} (x y : U) :
    Indistinguishable x y ↔ Indistinguishable (x : α) y := by
  simp_rw [indistinguishable_iff_closure, closure_subtype, image_singleton]

/-- Given a closed set `S` in a compact T₀ space,
there is some `x ∈ S` such that `{x}` is closed. -/
theorem IsClosed.exists_closed_singleton {α : Type _} [TopologicalSpace α] [T0Space α] [CompactSpace α] {S : Set α}
    (hS : IsClosed S) (hne : S.Nonempty) : ∃ x : α, x ∈ S ∧ IsClosed ({x} : Set α) := by
  obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne
  by_cases' hnt : ∃ (x y : α)(hx : x ∈ V)(hy : y ∈ V), x ≠ y
  · exfalso
    obtain ⟨x, y, hx, hy, hne⟩ := hnt
    obtain ⟨U, hU, hsep⟩ := T0Space.t0 _ _ hne
    have : ∀ z w : α hz : z ∈ V hw : w ∈ V hz' : z ∈ U hw' : ¬w ∈ U, False := by
      intro z w hz hw hz' hw'
      have uvne : (V ∩ Uᶜ).Nonempty := by
        use w
        simp only [hw, hw', Set.mem_inter_eq, not_false_iff, and_selfₓ, Set.mem_compl_eq]
      specialize hV (V ∩ Uᶜ) (Set.inter_subset_left _ _) uvne (IsClosed.inter Vcls (is_closed_compl_iff.mpr hU))
      have : V ⊆ Uᶜ := by
        rw [← hV]
        exact Set.inter_subset_right _ _
      exact this hz hz'
    cases hsep
    · exact this x y hx hy hsep.1 hsep.2
      
    · exact this y x hy hx hsep.1 hsep.2
      
    
  · push_neg  at hnt
    obtain ⟨z, hz⟩ := Vne
    refine' ⟨z, Vsub hz, _⟩
    convert Vcls
    ext
    simp only [Set.mem_singleton_iff, Set.mem_compl_eq]
    constructor
    · rintro rfl
      exact hz
      
    · exact fun hx => hnt x z hx hz
      
    

/-- Given an open `finset` `S` in a T₀ space, there is some `x ∈ S` such that `{x}` is open. -/
theorem exists_open_singleton_of_open_finset [T0Space α] (s : Finset α) (sne : s.Nonempty) (hso : IsOpen (s : Set α)) :
    ∃ x ∈ s, IsOpen ({x} : Set α) := by
  induction' s using Finset.strongInductionOn with s ihs
  by_cases' hs : Set.Subsingleton (s : Set α)
  · rcases sne with ⟨x, hx⟩
    refine' ⟨x, hx, _⟩
    have : (s : Set α) = {x} := hs.eq_singleton_of_mem hx
    rwa [this] at hso
    
  · dunfold Set.Subsingleton  at hs
    push_neg  at hs
    rcases hs with ⟨x, hx, y, hy, hxy⟩
    rcases T0Space.t0 x y hxy with ⟨U, hU, hxyU⟩
    wlog H : x ∈ U ∧ y ∉ U := hxyU using x y, y x
    obtain ⟨z, hzs, hz⟩ : ∃ z ∈ s.filter fun z => z ∈ U, IsOpen ({z} : Set α) := by
      refine' ihs _ (Finset.filter_ssubset.2 ⟨y, hy, H.2⟩) ⟨x, Finset.mem_filter.2 ⟨hx, H.1⟩⟩ _
      rw [Finset.coe_filter]
      exact IsOpen.inter hso hU
    exact ⟨z, (Finset.mem_filter.1 hzs).1, hz⟩
    

theorem exists_open_singleton_of_fintype [T0Space α] [f : Fintype α] [ha : Nonempty α] :
    ∃ x : α, IsOpen ({x} : Set α) := by
  refine' ha.elim fun x => _
  have : IsOpen ((Finset.univ : Finset α) : Set α) := by
    simp
  rcases exists_open_singleton_of_open_finset _ ⟨x, Finset.mem_univ x⟩ this with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

theorem t0_space_of_injective_of_continuous [TopologicalSpace β] {f : α → β} (hf : Function.Injective f)
    (hf' : Continuous f) [T0Space β] : T0Space α :=
  ⟨fun x y hxy =>
    let ⟨U, hU, hxyU⟩ := T0Space.t0 (f x) (f y) (hf.Ne hxy)
    ⟨f ⁻¹' U, hU.Preimage hf', hxyU⟩⟩

protected theorem Embedding.t0_space [TopologicalSpace β] [T0Space β] {f : α → β} (hf : Embedding f) : T0Space α :=
  t0_space_of_injective_of_continuous hf.inj hf.Continuous

instance Subtype.t0_space [T0Space α] {p : α → Prop} : T0Space (Subtype p) :=
  embedding_subtype_coe.T0Space

theorem t0_space_iff_or_not_mem_closure (α : Type u) [TopologicalSpace α] :
    T0Space α ↔ ∀ a b : α, a ≠ b → a ∉ Closure ({b} : Set α) ∨ b ∉ Closure ({a} : Set α) := by
  simp only [← not_and_distrib, t0_space_def, not_and]
  refine' forall₃_congrₓ fun a b _ => ⟨_, fun h => _⟩
  · rintro ⟨s, h₁, ⟨h₂, h₃ : b ∈ sᶜ⟩ | ⟨h₂, h₃ : a ∈ sᶜ⟩⟩ ha hb <;> rw [← is_closed_compl_iff] at h₁
    · exact (IsClosed.closure_subset_iff h₁).mpr (set.singleton_subset_iff.mpr h₃) ha h₂
      
    · exact (IsClosed.closure_subset_iff h₁).mpr (set.singleton_subset_iff.mpr h₃) hb h₂
      
    
  · by_cases' h' : a ∈ Closure ({b} : Set α)
    · exact ⟨Closure {a}ᶜ, is_closed_closure.1, Or.inr ⟨h h', not_not.mpr (subset_closure (Set.mem_singleton a))⟩⟩
      
    · exact ⟨Closure {b}ᶜ, is_closed_closure.1, Or.inl ⟨h', not_not.mpr (subset_closure (Set.mem_singleton b))⟩⟩
      
    

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class T1Space (α : Type u) [TopologicalSpace α] : Prop where
  t1 : ∀ x, IsClosed ({x} : Set α)

theorem is_closed_singleton [T1Space α] {x : α} : IsClosed ({x} : Set α) :=
  T1Space.t1 x

theorem is_open_compl_singleton [T1Space α] {x : α} : IsOpen ({x}ᶜ : Set α) :=
  is_closed_singleton.is_open_compl

theorem is_open_ne [T1Space α] {x : α} : IsOpen { y | y ≠ x } :=
  is_open_compl_singleton

theorem Ne.nhds_within_compl_singleton [T1Space α] {x y : α} (h : x ≠ y) : 𝓝[{y}ᶜ] x = 𝓝 x :=
  is_open_ne.nhds_within_eq h

theorem Ne.nhds_within_diff_singleton [T1Space α] {x y : α} (h : x ≠ y) (s : Set α) : 𝓝[s \ {y}] x = 𝓝[s] x := by
  rw [diff_eq, inter_comm, nhds_within_inter_of_mem]
  exact mem_nhds_within_of_mem_nhds (is_open_ne.mem_nhds h)

protected theorem Set.Finite.is_closed [T1Space α] {s : Set α} (hs : Set.Finite s) : IsClosed s := by
  rw [← bUnion_of_singleton s]
  exact is_closed_bUnion hs fun i hi => is_closed_singleton

theorem Filter.coclosed_compact_le_cofinite [T1Space α] : Filter.coclosedCompact α ≤ Filter.cofinite := fun s hs =>
  compl_compl s ▸ hs.IsCompact.compl_mem_coclosed_compact_of_is_closed hs.IsClosed

variable (α)

/-- In a `t1_space`, relatively compact sets form a bornology. Its cobounded filter is
`filter.coclosed_compact`. See also `bornology.in_compact` the bornology of sets contained
in a compact set. -/
def Bornology.relativelyCompact [T1Space α] : Bornology α where
  cobounded := Filter.coclosedCompact α
  le_cofinite := Filter.coclosed_compact_le_cofinite

variable {α}

theorem Bornology.relativelyCompact.is_bounded_iff [T1Space α] {s : Set α} :
    @Bornology.IsBounded _ (Bornology.relativelyCompact α) s ↔ IsCompact (Closure s) := by
  change sᶜ ∈ Filter.coclosedCompact α ↔ _
  rw [Filter.mem_coclosed_compact]
  constructor
  · rintro ⟨t, ht₁, ht₂, hst⟩
    rw [compl_subset_compl] at hst
    exact compact_of_is_closed_subset ht₂ is_closed_closure (closure_minimal hst ht₁)
    
  · intro h
    exact ⟨Closure s, is_closed_closure, h, compl_subset_compl.mpr subset_closure⟩
    

protected theorem Finset.is_closed [T1Space α] (s : Finset α) : IsClosed (s : Set α) :=
  s.finite_to_set.IsClosed

theorem t1_space_tfae (α : Type u) [TopologicalSpace α] :
    Tfae
      [T1Space α, ∀ x, IsClosed ({x} : Set α), ∀ x, IsOpen ({x}ᶜ : Set α), Continuous (@CofiniteTopology.of α),
        ∀ ⦃x y : α⦄, x ≠ y → {y}ᶜ ∈ 𝓝 x, ∀ ⦃x y : α⦄, x ≠ y → ∃ s ∈ 𝓝 x, y ∉ s,
        ∀ ⦃x y : α⦄, x ≠ y → ∃ (U : Set α)(hU : IsOpen U), x ∈ U ∧ y ∉ U, ∀ ⦃x y : α⦄, x ≠ y → Disjoint (𝓝 x) (pure y),
        ∀ ⦃x y : α⦄, x ≠ y → Disjoint (pure x) (𝓝 y)] :=
  by
  tfae_have 1 ↔ 2
  exact ⟨fun h => h.1, fun h => ⟨h⟩⟩
  tfae_have 2 ↔ 3
  · simp only [is_open_compl_iff]
    
  tfae_have 5 ↔ 3
  · refine' forall_swap.trans _
    simp only [is_open_iff_mem_nhds, mem_compl_iff, mem_singleton_iff]
    
  tfae_have 5 ↔ 6
  · simp only [← subset_compl_singleton_iff, exists_mem_subset_iff]
    
  tfae_have 5 ↔ 7
  · simp only [(nhds_basis_opens _).mem_iff, subset_compl_singleton_iff, exists_prop, And.assoc, And.left_comm]
    
  tfae_have 5 ↔ 8
  · simp only [← principal_singleton, disjoint_principal_right]
    
  tfae_have 8 ↔ 9
  exact
    forall_swap.trans
      (by
        simp only [Disjoint.comm, ne_comm])
  tfae_have 1 → 4
  · simp only [continuous_def, CofiniteTopology.is_open_iff']
    rintro H s (rfl | hs)
    exacts[is_open_empty, compl_compl s ▸ (@Set.Finite.is_closed _ _ H _ hs).is_open_compl]
    
  tfae_have 4 → 2
  exact fun h x => (CofiniteTopology.is_closed_iff.2 <| Or.inr (finite_singleton _)).Preimage h
  tfae_finish

theorem t1_space_iff_continuous_cofinite_of {α : Type _} [TopologicalSpace α] :
    T1Space α ↔ Continuous (@CofiniteTopology.of α) :=
  (t1_space_tfae α).out 0 3

theorem CofiniteTopology.continuous_of [T1Space α] : Continuous (@CofiniteTopology.of α) :=
  t1_space_iff_continuous_cofinite_of.mp ‹_›

theorem t1_space_iff_exists_open : T1Space α ↔ ∀ x y, x ≠ y → ∃ (U : Set α)(hU : IsOpen U), x ∈ U ∧ y ∉ U :=
  (t1_space_tfae α).out 0 6

theorem t1_space_iff_disjoint_pure_nhds : T1Space α ↔ ∀ ⦃x y : α⦄, x ≠ y → Disjoint (pure x) (𝓝 y) :=
  (t1_space_tfae α).out 0 8

theorem t1_space_iff_disjoint_nhds_pure : T1Space α ↔ ∀ ⦃x y : α⦄, x ≠ y → Disjoint (𝓝 x) (pure y) :=
  (t1_space_tfae α).out 0 7

theorem disjoint_pure_nhds [T1Space α] {x y : α} (h : x ≠ y) : Disjoint (pure x) (𝓝 y) :=
  t1_space_iff_disjoint_pure_nhds.mp ‹_› h

theorem disjoint_nhds_pure [T1Space α] {x y : α} (h : x ≠ y) : Disjoint (𝓝 x) (pure y) :=
  t1_space_iff_disjoint_nhds_pure.mp ‹_› h

instance {α : Type _} : T1Space (CofiniteTopology α) :=
  t1_space_iff_continuous_cofinite_of.mpr continuous_id

theorem t1_space_antitone {α : Type _} : Antitone (@T1Space α) := by
  simp only [Antitone, t1_space_iff_continuous_cofinite_of, continuous_iff_le_induced]
  exact fun t₁ t₂ h => h.trans

theorem continuous_within_at_update_of_ne [T1Space α] [DecidableEq α] [TopologicalSpace β] {f : α → β} {s : Set α}
    {x y : α} {z : β} (hne : y ≠ x) : ContinuousWithinAt (Function.update f x z) s y ↔ ContinuousWithinAt f s y :=
  EventuallyEq.congr_continuous_within_at
    (mem_nhds_within_of_mem_nhds <|
      (mem_of_superset (is_open_ne.mem_nhds hne)) fun y' hy' => Function.update_noteq hy' _ _)
    (Function.update_noteq hne _ _)

theorem continuous_at_update_of_ne [T1Space α] [DecidableEq α] [TopologicalSpace β] {f : α → β} {x y : α} {z : β}
    (hne : y ≠ x) : ContinuousAt (Function.update f x z) y ↔ ContinuousAt f y := by
  simp only [← continuous_within_at_univ, continuous_within_at_update_of_ne hne]

theorem continuous_on_update_iff [T1Space α] [DecidableEq α] [TopologicalSpace β] {f : α → β} {s : Set α} {x : α}
    {y : β} :
    ContinuousOn (Function.update f x y) s ↔ ContinuousOn f (s \ {x}) ∧ (x ∈ s → Tendsto f (𝓝[s \ {x}] x) (𝓝 y)) := by
  rw [ContinuousOn, ← and_forall_ne x, and_comm]
  refine' and_congr ⟨fun H z hz => _, fun H z hzx hzs => _⟩ (forall_congrₓ fun hxs => _)
  · specialize H z hz.2 hz.1
    rw [continuous_within_at_update_of_ne hz.2] at H
    exact H.mono (diff_subset _ _)
    
  · rw [continuous_within_at_update_of_ne hzx]
    refine' (H z ⟨hzs, hzx⟩).mono_of_mem (inter_mem_nhds_within _ _)
    exact is_open_ne.mem_nhds hzx
    
  · exact continuous_within_at_update_same
    

theorem t1_space_of_injective_of_continuous [TopologicalSpace β] {f : α → β} (hf : Function.Injective f)
    (hf' : Continuous f) [T1Space β] : T1Space α :=
  { t1 := by
      intro x
      rw [← Function.Injective.preimage_image hf {x}, image_singleton]
      exact (T1Space.t1 <| f x).Preimage hf' }

protected theorem Embedding.t1_space [TopologicalSpace β] [T1Space β] {f : α → β} (hf : Embedding f) : T1Space α :=
  t1_space_of_injective_of_continuous hf.inj hf.Continuous

instance Subtype.t1_space {α : Type u} [TopologicalSpace α] [T1Space α] {p : α → Prop} : T1Space (Subtype p) :=
  embedding_subtype_coe.T1Space

-- see Note [lower instance priority]
instance (priority := 100) T1Space.t0_space [T1Space α] : T0Space α :=
  ⟨fun x y h => ⟨{ z | z ≠ y }, is_open_ne, Or.inl ⟨h, not_not_intro rfl⟩⟩⟩

@[simp]
theorem compl_singleton_mem_nhds_iff [T1Space α] {x y : α} : {x}ᶜ ∈ 𝓝 y ↔ y ≠ x :=
  is_open_compl_singleton.mem_nhds_iff

theorem compl_singleton_mem_nhds [T1Space α] {x y : α} (h : y ≠ x) : {x}ᶜ ∈ 𝓝 y :=
  compl_singleton_mem_nhds_iff.mpr h

@[simp]
theorem closure_singleton [T1Space α] {a : α} : Closure ({a} : Set α) = {a} :=
  is_closed_singleton.closure_eq

theorem Set.Subsingleton.closure [T1Space α] {s : Set α} (hs : s.Subsingleton) : (Closure s).Subsingleton :=
  (hs.induction_on
      (by
        simp ))
    fun x => by
    simp

@[simp]
theorem subsingleton_closure [T1Space α] {s : Set α} : (Closure s).Subsingleton ↔ s.Subsingleton :=
  ⟨fun h => h.mono subset_closure, fun h => h.closure⟩

theorem is_closed_map_const {α β} [TopologicalSpace α] [TopologicalSpace β] [T1Space β] {y : β} :
    IsClosedMap (Function.const α y) := by
  apply IsClosedMap.of_nonempty
  intro s hs h2s
  simp_rw [h2s.image_const, is_closed_singleton]

theorem bInter_basis_nhds [T1Space α] {ι : Sort _} {p : ι → Prop} {s : ι → Set α} {x : α} (h : (𝓝 x).HasBasis p s) :
    (⋂ (i) (h : p i), s i) = {x} := by
  simp only [eq_singleton_iff_unique_mem, mem_Inter]
  refine' ⟨fun i hi => mem_of_mem_nhds <| h.mem_of_mem hi, fun y hy => _⟩
  contrapose! hy
  rcases h.mem_iff.1 (compl_singleton_mem_nhds hy.symm) with ⟨i, hi, hsub⟩
  exact ⟨i, hi, fun h => hsub h rfl⟩

@[simp]
theorem pure_le_nhds_iff [T1Space α] {a b : α} : pure a ≤ 𝓝 b ↔ a = b := by
  refine' ⟨fun h => _, fun h => h ▸ pure_le_nhds a⟩
  by_contra hab
  simpa only [mem_pure, mem_compl_iff, mem_singleton, not_true] using h (compl_singleton_mem_nhds <| Ne.symm hab)

@[simp]
theorem nhds_le_nhds_iff [T1Space α] {a b : α} : 𝓝 a ≤ 𝓝 b ↔ a = b :=
  ⟨fun h => pure_le_nhds_iff.mp <| (pure_le_nhds a).trans h, fun h => h ▸ le_rfl⟩

@[simp]
theorem compl_singleton_mem_nhds_set_iff [T1Space α] {x : α} {s : Set α} : {x}ᶜ ∈ 𝓝ˢ s ↔ x ∉ s := by
  rwa [is_open_compl_singleton.mem_nhds_set, subset_compl_singleton_iff]

@[simp]
theorem nhds_set_le_iff [T1Space α] {s t : Set α} : 𝓝ˢ s ≤ 𝓝ˢ t ↔ s ⊆ t := by
  refine' ⟨_, fun h => monotone_nhds_set h⟩
  simp_rw [Filter.le_def]
  intro h x hx
  specialize h ({x}ᶜ)
  simp_rw [compl_singleton_mem_nhds_set_iff]  at h
  by_contra hxt
  exact h hxt hx

@[simp]
theorem nhds_set_inj_iff [T1Space α] {s t : Set α} : 𝓝ˢ s = 𝓝ˢ t ↔ s = t := by
  simp_rw [le_antisymm_iffₓ]
  exact and_congr nhds_set_le_iff nhds_set_le_iff

theorem injective_nhds_set [T1Space α] : Function.Injective (𝓝ˢ : Set α → Filter α) := fun s t hst =>
  nhds_set_inj_iff.mp hst

theorem strict_mono_nhds_set [T1Space α] : StrictMono (𝓝ˢ : Set α → Filter α) :=
  monotone_nhds_set.strict_mono_of_injective injective_nhds_set

@[simp]
theorem nhds_le_nhds_set [T1Space α] {s : Set α} {x : α} : 𝓝 x ≤ 𝓝ˢ s ↔ x ∈ s := by
  rw [← nhds_set_singleton, nhds_set_le_iff, singleton_subset_iff]

/-- Removing a non-isolated point from a dense set, one still obtains a dense set. -/
theorem Dense.diff_singleton [T1Space α] {s : Set α} (hs : Dense s) (x : α) [NeBot (𝓝[≠] x)] : Dense (s \ {x}) :=
  hs.inter_of_open_right (dense_compl_singleton x) is_open_compl_singleton

/-- Removing a finset from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finset [T1Space α] [∀ x : α, NeBot (𝓝[≠] x)] {s : Set α} (hs : Dense s) (t : Finset α) :
    Dense (s \ t) := by
  induction' t using Finset.induction_on with x s hxs ih hd
  · simpa using hs
    
  · rw [Finset.coe_insert, ← union_singleton, ← diff_diff]
    exact ih.diff_singleton _
    

/-- Removing a finite set from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finite [T1Space α] [∀ x : α, NeBot (𝓝[≠] x)] {s : Set α} (hs : Dense s) {t : Set α} (ht : Finite t) :
    Dense (s \ t) := by
  convert hs.diff_finset ht.to_finset
  exact (finite.coe_to_finset _).symm

/-- If a function to a `t1_space` tends to some limit `b` at some point `a`, then necessarily
`b = f a`. -/
theorem eq_of_tendsto_nhds [TopologicalSpace β] [T1Space β] {f : α → β} {a : α} {b : β} (h : Tendsto f (𝓝 a) (𝓝 b)) :
    f a = b :=
  by_contra fun hfa : f a ≠ b =>
    have fact₁ : {f a}ᶜ ∈ 𝓝 b := compl_singleton_mem_nhds hfa.symm
    have fact₂ : Tendsto f (pure a) (𝓝 b) := h.comp (tendsto_id' <| pure_le_nhds a)
    fact₂ fact₁ (Eq.refl <| f a)

/-- To prove a function to a `t1_space` is continuous at some point `a`, it suffices to prove that
`f` admits *some* limit at `a`. -/
theorem continuous_at_of_tendsto_nhds [TopologicalSpace β] [T1Space β] {f : α → β} {a : α} {b : β}
    (h : Tendsto f (𝓝 a) (𝓝 b)) : ContinuousAt f a :=
  show Tendsto f (𝓝 a) (𝓝 <| f a) by
    rwa [eq_of_tendsto_nhds h]

theorem tendsto_const_nhds_iff [T1Space α] {l : Filter α} [NeBot l] {c d : α} : Tendsto (fun x => c) l (𝓝 d) ↔ c = d :=
  by
  simp_rw [tendsto, Filter.map_const, pure_le_nhds_iff]

/-- If the punctured neighborhoods of a point form a nontrivial filter, then any neighborhood is
infinite. -/
theorem infinite_of_mem_nhds {α} [TopologicalSpace α] [T1Space α] (x : α) [hx : NeBot (𝓝[≠] x)] {s : Set α}
    (hs : s ∈ 𝓝 x) : Set.Infinite s := by
  intro hsf
  have A : {x} ⊆ s := by
    simp only [singleton_subset_iff, mem_of_mem_nhds hs]
  have B : IsClosed (s \ {x}) := (hsf.subset (diff_subset _ _)).IsClosed
  have C : (s \ {x})ᶜ ∈ 𝓝 x := B.is_open_compl.mem_nhds fun h => h.2 rfl
  have D : {x} ∈ 𝓝 x := by
    simpa only [← diff_eq, diff_diff_cancel_left A] using inter_mem hs C
  rwa [← mem_interior_iff_mem_nhds, interior_singleton] at D

theorem discrete_of_t1_of_finite {X : Type _} [TopologicalSpace X] [T1Space X] [Fintype X] : DiscreteTopology X := by
  apply singletons_open_iff_discrete.mp
  intro x
  rw [← is_closed_compl_iff]
  exact (finite.of_fintype _).IsClosed

theorem singleton_mem_nhds_within_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    {x} ∈ 𝓝[s] x := by
  have : ({⟨x, hx⟩} : Set s) ∈ 𝓝 (⟨x, hx⟩ : s) := by
    simp [nhds_discrete]
  simpa only [nhds_within_eq_map_subtype_coe hx, image_singleton] using @image_mem_map _ _ _ (coe : s → α) _ this

/-- The neighbourhoods filter of `x` within `s`, under the discrete topology, is equal to
the pure `x` filter (which is the principal filter at the singleton `{x}`.) -/
theorem nhds_within_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) : 𝓝[s] x = pure x :=
  le_antisymmₓ (le_pure_iff.2 <| singleton_mem_nhds_within_of_mem_discrete hx) (pure_le_nhds_within hx)

theorem Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete {ι : Type _} {p : ι → Prop} {t : ι → Set α}
    {s : Set α} [DiscreteTopology s] {x : α} (hb : (𝓝 x).HasBasis p t) (hx : x ∈ s) :
    ∃ (i : _)(hi : p i), t i ∩ s = {x} := by
  rcases(nhds_within_has_basis hb s).mem_iff.1 (singleton_mem_nhds_within_of_mem_discrete hx) with ⟨i, hi, hix⟩
  exact ⟨i, hi, subset.antisymm hix <| singleton_subset_iff.2 ⟨mem_of_mem_nhds <| hb.mem_of_mem hi, hx⟩⟩

/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`.  -/
theorem nhds_inter_eq_singleton_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    ∃ U ∈ 𝓝 x, U ∩ s = {x} := by
  simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hx

/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (ie. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
theorem disjoint_nhds_within_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) :
    ∃ U ∈ 𝓝[≠] x, Disjoint U s :=
  let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hx
  ⟨{x}ᶜ ∩ V, inter_mem_nhds_within _ h,
    disjoint_iff_inter_eq_empty.mpr
      (by
        rw [inter_assoc, h', compl_inter_self])⟩

/-- Let `X` be a topological space and let `s, t ⊆ X` be two subsets.  If there is an inclusion
`t ⊆ s`, then the topological space structure on `t` induced by `X` is the same as the one
obtained by the induced topological space structure on `s`. -/
theorem TopologicalSpace.subset_trans {X : Type _} [tX : TopologicalSpace X] {s t : Set X} (ts : t ⊆ s) :
    (Subtype.topologicalSpace : TopologicalSpace t) =
      (Subtype.topologicalSpace : TopologicalSpace s).induced (Set.inclusion ts) :=
  by
  change tX.induced ((coe : s → X) ∘ Set.inclusion ts) = TopologicalSpace.induced (Set.inclusion ts) (tX.induced _)
  rw [← induced_compose]

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
theorem discrete_topology_iff_nhds {X : Type _} [TopologicalSpace X] :
    DiscreteTopology X ↔ (nhds : X → Filter X) = pure := by
  constructor
  · intro hX
    exact nhds_discrete X
    
  · intro h
    constructor
    apply eq_of_nhds_eq_nhds
    simp [h, nhds_bot]
    

/-- The topology pulled-back under an inclusion `f : X → Y` from the discrete topology (`⊥`) is the
discrete topology.
This version does not assume the choice of a topology on either the source `X`
nor the target `Y` of the inclusion `f`. -/
theorem induced_bot {X Y : Type _} {f : X → Y} (hf : Function.Injective f) : TopologicalSpace.induced f ⊥ = ⊥ :=
  eq_of_nhds_eq_nhds
    (by
      simp [nhds_induced, ← Set.image_singleton, hf.preimage_image, nhds_bot])

/-- The topology induced under an inclusion `f : X → Y` from the discrete topological space `Y`
is the discrete topology on `X`. -/
theorem discrete_topology_induced {X Y : Type _} [tY : TopologicalSpace Y] [DiscreteTopology Y] {f : X → Y}
    (hf : Function.Injective f) : @DiscreteTopology X (TopologicalSpace.induced f tY) := by
  constructor
  rw [DiscreteTopology.eq_bot Y]
  exact induced_bot hf

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.  -/
theorem DiscreteTopology.of_subset {X : Type _} [TopologicalSpace X] {s t : Set X} (ds : DiscreteTopology s)
    (ts : t ⊆ s) : DiscreteTopology t := by
  rw [TopologicalSpace.subset_trans ts, ds.eq_bot]
  exact { eq_bot := induced_bot (Set.inclusion_injective ts) }

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
@[mk_iff]
class T2Space (α : Type u) [TopologicalSpace α] : Prop where
  t2 : ∀ x y, x ≠ y → ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

/-- Two different points can be separated by open sets. -/
theorem t2_separation [T2Space α] {x y : α} (h : x ≠ y) :
    ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
  T2Space.t2 x y h

/-- A finite set can be separated by open sets. -/
theorem t2_separation_finset [T2Space α] (s : Finset α) :
    ∃ f : α → Set α, Set.PairwiseDisjoint (↑s) f ∧ ∀, ∀ x ∈ s, ∀, x ∈ f x ∧ IsOpen (f x) :=
  Finset.induction_on s
    (by
      simp )
    (by
      rintro t s ht ⟨f, hf, hf'⟩
      have hty : ∀ y : s, t ≠ y := by
        rintro y rfl
        exact ht y.2
      choose u v hu hv htu hxv huv using fun h : t ≠ x => t2_separation h
      refine' ⟨fun x => if ht : t = x then ⋂ y : s, u (hty y) else f x ∩ v ht, _, _⟩
      · rintro x hx₁ y hy₁ hxy a ⟨hx, hy⟩
        rw [Finset.mem_coe, Finset.mem_insert, eq_comm] at hx₁ hy₁
        rcases eq_or_ne t x with (rfl | hx₂) <;> rcases eq_or_ne t y with (rfl | hy₂)
        · exact hxy rfl
          
        · simp_rw [dif_pos rfl, mem_Inter]  at hx
          simp_rw [dif_neg hy₂]  at hy
          rw [bot_eq_empty, ← huv hy₂]
          exact ⟨hx ⟨y, hy₁.resolve_left hy₂⟩, hy.2⟩
          
        · simp_rw [dif_neg hx₂]  at hx
          simp_rw [dif_pos rfl, mem_Inter]  at hy
          rw [bot_eq_empty, ← huv hx₂]
          exact ⟨hy ⟨x, hx₁.resolve_left hx₂⟩, hx.2⟩
          
        · simp_rw [dif_neg hx₂]  at hx
          simp_rw [dif_neg hy₂]  at hy
          exact hf (hx₁.resolve_left hx₂) (hy₁.resolve_left hy₂) hxy ⟨hx.1, hy.1⟩
          
        
      · intro x hx
        split_ifs with ht
        · refine' ⟨mem_Inter.2 fun y => _, is_open_Inter fun y => hu (hty y)⟩
          rw [← ht]
          exact htu (hty y)
          
        · have hx := hf' x ((Finset.mem_insert.1 hx).resolve_left (Ne.symm ht))
          exact ⟨⟨hx.1, hxv ht⟩, IsOpen.inter hx.2 (hv ht)⟩
          
        )

-- see Note [lower instance priority]
instance (priority := 100) T2Space.t1_space [T2Space α] : T1Space α :=
  ⟨fun x =>
    is_open_compl_iff.1 <|
      is_open_iff_forall_mem_open.2 fun y hxy =>
        let ⟨u, v, hu, hv, hyu, hxv, huv⟩ := t2_separation (mt mem_singleton_of_eq hxy)
        ⟨u, fun z hz1 hz2 => (ext_iff.1 huv x).1 ⟨mem_singleton_iff.1 hz2 ▸ hz1, hxv⟩, hu, hyu⟩⟩

theorem eq_of_nhds_ne_bot [ht : T2Space α] {x y : α} (h : NeBot (𝓝 x⊓𝓝 y)) : x = y :=
  Classical.by_contradiction fun this : x ≠ y =>
    let ⟨u, v, hu, hv, hx, hy, huv⟩ := T2Space.t2 x y this
    absurd huv <| (inf_ne_bot_iff.1 h (IsOpen.mem_nhds hu hx) (IsOpen.mem_nhds hv hy)).ne_empty

/-- A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter. -/
theorem t2_iff_nhds : T2Space α ↔ ∀ {x y : α}, NeBot (𝓝 x⊓𝓝 y) → x = y :=
  ⟨fun h => fun x y => eq_of_nhds_ne_bot, fun h =>
    ⟨fun x y xy =>
      have : 𝓝 x⊓𝓝 y = ⊥ := not_ne_bot.1 <| mt h xy
      let ⟨u', hu', v', hv', u'v'⟩ := empty_mem_iff_bot.mpr this
      let ⟨u, uu', uo, hu⟩ := mem_nhds_iff.mp hu'
      let ⟨v, vv', vo, hv⟩ := mem_nhds_iff.mp hv'
      ⟨u, v, uo, vo, hu, hv, by
        rw [← subset_empty_iff, u'v']
        exact inter_subset_inter uu' vv'⟩⟩⟩

theorem t2_space_iff_nhds : T2Space α ↔ ∀ {x y : α}, x ≠ y → ∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 y, U ∩ V = ∅ := by
  constructor
  · rintro ⟨h⟩ x y hxy
    rcases h x y hxy with ⟨u, v, u_op, v_op, hx, hy, H⟩
    exact ⟨u, u_op.mem_nhds hx, v, v_op.mem_nhds hy, H⟩
    
  · refine' fun h => ⟨fun x y hxy => _⟩
    rcases h hxy with ⟨u, u_in, v, v_in, H⟩
    rcases mem_nhds_iff.mp u_in with ⟨U, hUu, U_op, hxU⟩
    rcases mem_nhds_iff.mp v_in with ⟨V, hVv, V_op, hyV⟩
    refine' ⟨U, V, U_op, V_op, hxU, hyV, Set.eq_empty_of_subset_empty _⟩
    rw [← H]
    exact Set.inter_subset_inter hUu hVv
    

theorem t2_separation_nhds [T2Space α] {x y : α} (h : x ≠ y) : ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ u ∩ v = ∅ :=
  let ⟨u, v, open_u, open_v, x_in, y_in, huv⟩ := t2_separation h
  ⟨u, v, open_u.mem_nhds x_in, open_v.mem_nhds y_in, huv⟩

theorem t2_separation_compact_nhds [LocallyCompactSpace α] [T2Space α] {x y : α} (h : x ≠ y) :
    ∃ u v, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ IsCompact u ∧ IsCompact v ∧ u ∩ v = ∅ := by
  obtain ⟨u₀, v₀, u₀_in, v₀_in, hu₀v₀⟩ := t2_separation_nhds h
  obtain ⟨K₀, K₀_in, K₀_u₀, hK₀⟩ := local_compact_nhds u₀_in
  obtain ⟨L₀, L₀_in, L₀_u₀, hL₀⟩ := local_compact_nhds v₀_in
  use K₀, L₀, K₀_in, L₀_in, hK₀, hL₀
  apply Set.eq_empty_of_subset_empty
  rw [← hu₀v₀]
  exact Set.inter_subset_inter K₀_u₀ L₀_u₀

theorem t2_iff_ultrafilter : T2Space α ↔ ∀ {x y : α} f : Ultrafilter α, ↑f ≤ 𝓝 x → ↑f ≤ 𝓝 y → x = y :=
  t2_iff_nhds.trans <| by
    simp only [← exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp_distrib]

theorem is_closed_diagonal [T2Space α] : IsClosed (Diagonal α) := by
  refine' is_closed_iff_cluster_pt.mpr _
  rintro ⟨a₁, a₂⟩ h
  refine' eq_of_nhds_ne_bot ⟨fun this : 𝓝 a₁⊓𝓝 a₂ = ⊥ => h.ne _⟩
  obtain ⟨t₁, ht₁ : t₁ ∈ 𝓝 a₁, t₂, ht₂ : t₂ ∈ 𝓝 a₂, h' : t₁ ∩ t₂ = ∅⟩ := inf_eq_bot_iff.1 this
  rw [inf_principal_eq_bot, nhds_prod_eq]
  apply mem_of_superset (prod_mem_prod ht₁ ht₂)
  rintro ⟨x, y⟩ ⟨x_in, y_in⟩ (heq : x = y)
  rw [← HEq] at *
  have : x ∈ t₁ ∩ t₂ := ⟨x_in, y_in⟩
  rwa [h'] at this

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (t «expr ⊆ » «expr ᶜ»(diagonal α))
theorem t2_iff_is_closed_diagonal : T2Space α ↔ IsClosed (Diagonal α) := by
  constructor
  · intro h
    exact is_closed_diagonal
    
  · intro h
    constructor
    intro x y hxy
    have : (x, y) ∈ diagonal αᶜ := by
      rwa [mem_compl_iff]
    obtain ⟨t, t_sub, t_op, xyt⟩ : ∃ (t : _)(_ : t ⊆ diagonal αᶜ), IsOpen t ∧ (x, y) ∈ t :=
      is_open_iff_forall_mem_open.mp h.is_open_compl _ this
    rcases is_open_prod_iff.mp t_op x y xyt with ⟨U, V, U_op, V_op, xU, yV, H⟩
    use U, V, U_op, V_op, xU, yV
    have := subset.trans H t_sub
    rw [eq_empty_iff_forall_not_mem]
    rintro z ⟨zU, zV⟩
    have : ¬(z, z) ∈ diagonal α := this (mk_mem_prod zU zV)
    exact this rfl
    

section Separated

open Separated Finset

theorem finset_disjoint_finset_opens_of_t2 [T2Space α] : ∀ s t : Finset α, Disjoint s t → Separated (s : Set α) t := by
  refine' induction_on_union _ (fun a b hi d => (hi d.symm).symm) (fun a d => empty_right a) (fun a b ab => _) _
  · obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := t2_separation (Finset.disjoint_singleton.1 ab)
    refine' ⟨U, V, oU, oV, _, _, set.disjoint_iff_inter_eq_empty.mpr UV⟩ <;> exact singleton_subset_set_iff.mpr ‹_›
    
  · intro a b c ac bc d
    apply_mod_cast union_left (ac (disjoint_of_subset_left (a.subset_union_left b) d)) (bc _)
    exact disjoint_of_subset_left (a.subset_union_right b) d
    

theorem point_disjoint_finset_opens_of_t2 [T2Space α] {x : α} {s : Finset α} (h : x ∉ s) : Separated ({x} : Set α) s :=
  by
  exact_mod_cast finset_disjoint_finset_opens_of_t2 {x} s (finset.disjoint_singleton_left.mpr h)

end Separated

theorem tendsto_nhds_unique [T2Space α] {f : β → α} {l : Filter β} {a b : α} [NeBot l] (ha : Tendsto f l (𝓝 a))
    (hb : Tendsto f l (𝓝 b)) : a = b :=
  eq_of_nhds_ne_bot <| ne_bot_of_le <| le_inf ha hb

theorem tendsto_nhds_unique' [T2Space α] {f : β → α} {l : Filter β} {a b : α} (hl : NeBot l) (ha : Tendsto f l (𝓝 a))
    (hb : Tendsto f l (𝓝 b)) : a = b :=
  eq_of_nhds_ne_bot <| ne_bot_of_le <| le_inf ha hb

theorem tendsto_nhds_unique_of_eventually_eq [T2Space α] {f g : β → α} {l : Filter β} {a b : α} [NeBot l]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) (hfg : f =ᶠ[l] g) : a = b :=
  tendsto_nhds_unique (ha.congr' hfg) hb

theorem tendsto_nhds_unique_of_frequently_eq [T2Space α] {f g : β → α} {l : Filter β} {a b : α} (ha : Tendsto f l (𝓝 a))
    (hb : Tendsto g l (𝓝 b)) (hfg : ∃ᶠ x in l, f x = g x) : a = b :=
  have : ∃ᶠ z : α × α in 𝓝 (a, b), z.1 = z.2 := (ha.prod_mk_nhds hb).Frequently hfg
  not_not.1 fun hne => this (is_closed_diagonal.is_open_compl.mem_nhds hne)

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of closures
  empty, one containing `x` and the other `y` . -/
class T25Space (α : Type u) [TopologicalSpace α] : Prop where
  t2_5 : ∀ x y h : x ≠ y, ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ Closure U ∩ Closure V = ∅ ∧ x ∈ U ∧ y ∈ V

-- see Note [lower instance priority]
instance (priority := 100) T25Space.t2_space [T25Space α] : T2Space α :=
  ⟨fun x y hxy =>
    let ⟨U, V, hU, hV, hUV, hh⟩ := T25Space.t2_5 x y hxy
    ⟨U, V, hU, hV, hh.1, hh.2,
      subset_eq_empty (powerset_mono.mpr (closure_inter_subset_inter_closure U V) subset_closure) hUV⟩⟩

section limₓ

variable [T2Space α] {f : Filter α}

/-!
### Properties of `Lim` and `lim`

In this section we use explicit `nonempty α` instances for `Lim` and `lim`. This way the lemmas
are useful without a `nonempty α` instance.
-/


theorem Lim_eq {a : α} [NeBot f] (h : f ≤ 𝓝 a) : @lim _ _ ⟨a⟩ f = a :=
  tendsto_nhds_unique (le_nhds_Lim ⟨a, h⟩) h

theorem Lim_eq_iff [NeBot f] (h : ∃ a : α, f ≤ nhds a) {a} : @lim _ _ ⟨a⟩ f = a ↔ f ≤ 𝓝 a :=
  ⟨fun c => c ▸ le_nhds_Lim h, Lim_eq⟩

theorem Ultrafilter.Lim_eq_iff_le_nhds [CompactSpace α] {x : α} {F : Ultrafilter α} : F.lim = x ↔ ↑F ≤ 𝓝 x :=
  ⟨fun h => h ▸ F.le_nhds_Lim, Lim_eq⟩

theorem is_open_iff_ultrafilter' [CompactSpace α] (U : Set α) : IsOpen U ↔ ∀ F : Ultrafilter α, F.lim ∈ U → U ∈ F.1 :=
  by
  rw [is_open_iff_ultrafilter]
  refine' ⟨fun h F hF => h F.lim hF F F.le_nhds_Lim, _⟩
  intro cond x hx f h
  rw [← Ultrafilter.Lim_eq_iff_le_nhds.2 h] at hx
  exact cond _ hx

theorem Filter.Tendsto.lim_eq {a : α} {f : Filter β} [NeBot f] {g : β → α} (h : Tendsto g f (𝓝 a)) :
    @limₓ _ _ _ ⟨a⟩ f g = a :=
  Lim_eq h

theorem Filter.lim_eq_iff {f : Filter β} [NeBot f] {g : β → α} (h : ∃ a, Tendsto g f (𝓝 a)) {a} :
    @limₓ _ _ _ ⟨a⟩ f g = a ↔ Tendsto g f (𝓝 a) :=
  ⟨fun c => c ▸ tendsto_nhds_lim h, Filter.Tendsto.lim_eq⟩

theorem Continuous.lim_eq [TopologicalSpace β] {f : β → α} (h : Continuous f) (a : β) :
    @limₓ _ _ _ ⟨f a⟩ (𝓝 a) f = f a :=
  (h.Tendsto a).lim_eq

@[simp]
theorem Lim_nhds (a : α) : @lim _ _ ⟨a⟩ (𝓝 a) = a :=
  Lim_eq le_rfl

@[simp]
theorem lim_nhds_id (a : α) : @limₓ _ _ _ ⟨a⟩ (𝓝 a) id = a :=
  Lim_nhds a

@[simp]
theorem Lim_nhds_within {a : α} {s : Set α} (h : a ∈ Closure s) : @lim _ _ ⟨a⟩ (𝓝[s] a) = a :=
  have : ne_bot (𝓝[s] a) := mem_closure_iff_cluster_pt.1 h
  Lim_eq inf_le_left

@[simp]
theorem lim_nhds_within_id {a : α} {s : Set α} (h : a ∈ Closure s) : @limₓ _ _ _ ⟨a⟩ (𝓝[s] a) id = a :=
  Lim_nhds_within h

end limₓ

/-!
### `t2_space` constructions

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : α` can be separated by open neighborhoods
  provided that there exists a continuous map `f : α → β` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_open_embedding` says that for an open embedding `f : α → β` of a Hausdorff space
  `α`, the images of two distinct points `x y : α`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/


-- see Note [lower instance priority]
instance (priority := 100) t2_space_discrete {α : Type _} [TopologicalSpace α] [DiscreteTopology α] : T2Space α where
  t2 := fun x y hxy =>
    ⟨{x}, {y}, is_open_discrete _, is_open_discrete _, rfl, rfl,
      eq_empty_iff_forall_not_mem.2 <| by
        intro z hz <;> cases eq_of_mem_singleton hz.1 <;> cases eq_of_mem_singleton hz.2 <;> cc⟩

theorem separated_by_continuous {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    {f : α → β} (hf : Continuous f) {x y : α} (h : f x ≠ f y) :
    ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f ⁻¹' u, f ⁻¹' v, uo.Preimage hf, vo.Preimage hf, xu, yv, by
    rw [← preimage_inter, uv, preimage_empty]⟩

theorem separated_by_open_embedding {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] [T2Space α] {f : α → β}
    (hf : OpenEmbedding f) {x y : α} (h : x ≠ y) : ∃ u v : Set β, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ f y ∈ v ∧ u ∩ v = ∅ :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f '' u, f '' v, hf.IsOpenMap _ uo, hf.IsOpenMap _ vo, mem_image_of_mem _ xu, mem_image_of_mem _ yv, by
    rw [image_inter hf.inj, uv, image_empty]⟩

instance {α : Type _} {p : α → Prop} [t : TopologicalSpace α] [T2Space α] : T2Space (Subtype p) :=
  ⟨fun x y h => separated_by_continuous continuous_subtype_val (mt Subtype.eq h)⟩

instance {α : Type _} {β : Type _} [t₁ : TopologicalSpace α] [T2Space α] [t₂ : TopologicalSpace β] [T2Space β] :
    T2Space (α × β) :=
  ⟨fun h =>
    Or.elim (not_and_distrib.mp (mt Prod.ext_iff.mpr h)) (fun h₁ => separated_by_continuous continuous_fst h₁) fun h₂ =>
      separated_by_continuous continuous_snd h₂⟩

theorem Embedding.t2_space [TopologicalSpace β] [T2Space β] {f : α → β} (hf : Embedding f) : T2Space α :=
  ⟨fun x y h => separated_by_continuous hf.Continuous (hf.inj.Ne h)⟩

instance {α : Type _} {β : Type _} [t₁ : TopologicalSpace α] [T2Space α] [t₂ : TopologicalSpace β] [T2Space β] :
    T2Space (Sum α β) := by
  constructor
  rintro (x | x) (y | y) h
  · replace h : x ≠ y := fun c => (c.subst h) rfl
    exact separated_by_open_embedding open_embedding_inl h
    
  · exact ⟨_, _, is_open_range_inl, is_open_range_inr, ⟨x, rfl⟩, ⟨y, rfl⟩, range_inl_inter_range_inr⟩
    
  · exact ⟨_, _, is_open_range_inr, is_open_range_inl, ⟨x, rfl⟩, ⟨y, rfl⟩, range_inr_inter_range_inl⟩
    
  · replace h : x ≠ y := fun c => (c.subst h) rfl
    exact separated_by_open_embedding open_embedding_inr h
    

instance Pi.t2_space {α : Type _} {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] [∀ a, T2Space (β a)] :
    T2Space (∀ a, β a) :=
  ⟨fun x y h =>
    let ⟨i, hi⟩ := not_forall.mp (mt funext h)
    separated_by_continuous (continuous_apply i) hi⟩

instance Sigma.t2_space {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] [∀ a, T2Space (α a)] :
    T2Space (Σi, α i) := by
  constructor
  rintro ⟨i, x⟩ ⟨j, y⟩ neq
  rcases em (i = j) with (rfl | h)
  · replace neq : x ≠ y := fun c => (c.subst neq) rfl
    exact separated_by_open_embedding open_embedding_sigma_mk neq
    
  · exact
      ⟨_, _, is_open_range_sigma_mk, is_open_range_sigma_mk, ⟨x, rfl⟩, ⟨y, rfl⟩, by
        tidy⟩
    

variable [TopologicalSpace β]

theorem is_closed_eq [T2Space α] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { x : β | f x = g x } :=
  continuous_iff_is_closed.mp (hf.prod_mk hg) _ is_closed_diagonal

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. See also
`set.eq_on.of_subset_closure` for a more general version. -/
theorem Set.EqOn.closure [T2Space α] {s : Set β} {f g : β → α} (h : EqOn f g s) (hf : Continuous f)
    (hg : Continuous g) : EqOn f g (Closure s) :=
  closure_minimal h (is_closed_eq hf hg)

/-- If two continuous functions are equal on a dense set, then they are equal. -/
theorem Continuous.ext_on [T2Space α] {s : Set β} (hs : Dense s) {f g : β → α} (hf : Continuous f) (hg : Continuous g)
    (h : EqOn f g s) : f = g :=
  funext fun x => h.closure hf hg (hs x)

/-- If `f x = g x` for all `x ∈ s` and `f`, `g` are continuous on `t`, `s ⊆ t ⊆ closure s`, then
`f x = g x` for all `x ∈ t`. See also `set.eq_on.closure`. -/
theorem Set.EqOn.of_subset_closure [T2Space α] {s t : Set β} {f g : β → α} (h : EqOn f g s) (hf : ContinuousOn f t)
    (hg : ContinuousOn g t) (hst : s ⊆ t) (hts : t ⊆ Closure s) : EqOn f g t := by
  intro x hx
  have : (𝓝[s] x).ne_bot := mem_closure_iff_cluster_pt.mp (hts hx)
  exact
    tendsto_nhds_unique_of_eventually_eq ((hf x hx).mono_left <| nhds_within_mono _ hst)
      ((hg x hx).mono_left <| nhds_within_mono _ hst) (h.eventually_eq_of_mem self_mem_nhds_within)

theorem Function.LeftInverse.closed_range [T2Space α] {f : α → β} {g : β → α} (h : Function.LeftInverse f g)
    (hf : Continuous f) (hg : Continuous g) : IsClosed (Range g) :=
  have : EqOn (g ∘ f) id (Closure <| Range g) := h.right_inv_on_range.EqOn.closure (hg.comp hf) continuous_id
  is_closed_of_closure_subset fun x hx =>
    calc
      x = g (f x) := (this hx).symm
      _ ∈ _ := mem_range_self _
      

theorem Function.LeftInverse.closed_embedding [T2Space α] {f : α → β} {g : β → α} (h : Function.LeftInverse f g)
    (hf : Continuous f) (hg : Continuous g) : ClosedEmbedding g :=
  ⟨h.Embedding hf hg, h.closed_range hf hg⟩

theorem diagonal_eq_range_diagonal_map {α : Type _} : { p : α × α | p.1 = p.2 } = Range fun x => (x, x) :=
  ext fun p =>
    Iff.intro (fun h => ⟨p.1, Prod.ext_iff.2 ⟨rfl, h⟩⟩) fun ⟨x, hx⟩ =>
      show p.1 = p.2 by
        rw [← hx]

theorem prod_subset_compl_diagonal_iff_disjoint {α : Type _} {s t : Set α} :
    s ×ˢ t ⊆ { p : α × α | p.1 = p.2 }ᶜ ↔ s ∩ t = ∅ := by
  rw [eq_empty_iff_forall_not_mem, subset_compl_comm, diagonal_eq_range_diagonal_map, range_subset_iff] <;> simp

theorem compact_compact_separated [T2Space α] {s t : Set α} (hs : IsCompact s) (ht : IsCompact t) (hst : s ∩ t = ∅) :
    ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅ := by
  simp only [prod_subset_compl_diagonal_iff_disjoint.symm] at hst⊢ <;>
    exact generalized_tube_lemma hs ht is_closed_diagonal.is_open_compl hst

/-- In a `t2_space`, every compact set is closed. -/
theorem IsCompact.is_closed [T2Space α] {s : Set α} (hs : IsCompact s) : IsClosed s :=
  is_open_compl_iff.1 <|
    is_open_iff_forall_mem_open.mpr fun x hx =>
      let ⟨u, v, uo, vo, su, xv, uv⟩ :=
        compact_compact_separated hs (is_compact_singleton : IsCompact {x})
          (by
            rwa [inter_comm, ← subset_compl_iff_disjoint, singleton_subset_iff])
      have : v ⊆ sᶜ := subset_compl_comm.mp (Subset.trans su (subset_compl_iff_disjoint.mpr uv))
      ⟨v, this, vo, by
        simpa using xv⟩

@[simp]
theorem Filter.coclosed_compact_eq_cocompact [T2Space α] : coclosedCompact α = cocompact α := by
  simp [coclosed_compact, cocompact, infi_and', and_iff_right_of_imp IsCompact.is_closed]

@[simp]
theorem Bornology.relatively_compact_eq_in_compact [T2Space α] :
    Bornology.relativelyCompact α = Bornology.inCompact α := by
  rw [Bornology.ext_iff] <;> exact Filter.coclosed_compact_eq_cocompact

/-- If `V : ι → set α` is a decreasing family of compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhd_of_compact'` where we
don't need to assume each `V i` closed because it follows from compactness since `α` is
assumed to be Hausdorff. -/
theorem exists_subset_nhd_of_compact [T2Space α] {ι : Type _} [Nonempty ι] {V : ι → Set α} (hV : Directed (· ⊇ ·) V)
    (hV_cpct : ∀ i, IsCompact (V i)) {U : Set α} (hU : ∀, ∀ x ∈ ⋂ i, V i, ∀, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhd_of_compact' hV hV_cpct (fun i => (hV_cpct i).IsClosed) hU

theorem CompactExhaustion.is_closed [T2Space α] (K : CompactExhaustion α) (n : ℕ) : IsClosed (K n) :=
  (K.IsCompact n).IsClosed

theorem IsCompact.inter [T2Space α] {s t : Set α} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∩ t) :=
  hs.inter_right <| ht.IsClosed

theorem compact_closure_of_subset_compact [T2Space α] {s t : Set α} (ht : IsCompact t) (h : s ⊆ t) :
    IsCompact (Closure s) :=
  compact_of_is_closed_subset ht is_closed_closure (closure_minimal h ht.IsClosed)

@[simp]
theorem exists_compact_superset_iff [T2Space α] {s : Set α} : (∃ K, IsCompact K ∧ s ⊆ K) ↔ IsCompact (Closure s) :=
  ⟨fun ⟨K, hK, hsK⟩ => compact_closure_of_subset_compact hK hsK, fun h => ⟨Closure s, h, subset_closure⟩⟩

theorem image_closure_of_compact [T2Space β] {s : Set α} (hs : IsCompact (Closure s)) {f : α → β}
    (hf : ContinuousOn f (Closure s)) : f '' Closure s = Closure (f '' s) :=
  Subset.antisymm hf.image_closure <|
    closure_minimal (image_subset f subset_closure) (hs.image_of_continuous_on hf).IsClosed

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
theorem IsCompact.binary_compact_cover [T2Space α] {K U V : Set α} (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V)
    (h2K : K ⊆ U ∪ V) : ∃ K₁ K₂ : Set α, IsCompact K₁ ∧ IsCompact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ := by
  rcases compact_compact_separated (hK.diff hU) (hK.diff hV)
      (by
        rwa [diff_inter_diff, diff_eq_empty]) with
    ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩
  refine'
    ⟨_, _, hK.diff h1O₁, hK.diff h1O₂, by
      rwa [diff_subset_comm], by
      rwa [diff_subset_comm], by
      rw [← diff_inter, hO, diff_empty]⟩

theorem Continuous.is_closed_map [CompactSpace α] [T2Space β] {f : α → β} (h : Continuous f) : IsClosedMap f :=
  fun s hs => (hs.IsCompact.Image h).IsClosed

theorem Continuous.closed_embedding [CompactSpace α] [T2Space β] {f : α → β} (h : Continuous f)
    (hf : Function.Injective f) : ClosedEmbedding f :=
  closed_embedding_of_continuous_injective_closed h hf h.IsClosedMap

section

open Finset Function

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
theorem IsCompact.finite_compact_cover [T2Space α] {s : Set α} (hs : IsCompact s) {ι} (t : Finset ι) (U : ι → Set α)
    (hU : ∀, ∀ i ∈ t, ∀, IsOpen (U i)) (hsC : s ⊆ ⋃ i ∈ t, U i) :
    ∃ K : ι → Set α, (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U i) ∧ s = ⋃ i ∈ t, K i := by
  classical
  induction' t using Finset.induction with x t hx ih generalizing U hU s hs hsC
  · refine' ⟨fun _ => ∅, fun i => is_compact_empty, fun i => empty_subset _, _⟩
    simpa only [subset_empty_iff, Union_false, Union_empty] using hsC
    
  simp only [Finset.set_bUnion_insert] at hsC
  simp only [Finset.mem_insert] at hU
  have hU' : ∀, ∀ i ∈ t, ∀, IsOpen (U i) := fun i hi => hU i (Or.inr hi)
  rcases hs.binary_compact_cover (hU x (Or.inl rfl)) (is_open_bUnion hU') hsC with ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩
  rcases ih U hU' h1K₂ h2K₂ with ⟨K, h1K, h2K, h3K⟩
  refine' ⟨update K x K₁, _, _, _⟩
  · intro i
    by_cases' hi : i = x
    · simp only [update_same, hi, h1K₁]
      
    · rw [← Ne.def] at hi
      simp only [update_noteq hi, h1K]
      
    
  · intro i
    by_cases' hi : i = x
    · simp only [update_same, hi, h2K₁]
      
    · rw [← Ne.def] at hi
      simp only [update_noteq hi, h2K]
      
    
  · simp only [set_bUnion_insert_update _ hx, hK, h3K]
    

end

theorem locally_compact_of_compact_nhds [T2Space α] (h : ∀ x : α, ∃ s, s ∈ 𝓝 x ∧ IsCompact s) : LocallyCompactSpace α :=
  ⟨fun x n hn =>
    let ⟨u, un, uo, xu⟩ := mem_nhds_iff.mp hn
    let ⟨k, kx, kc⟩ := h x
    -- K is compact but not necessarily contained in N.
    -- K \ U is again compact and doesn't contain x, so
    -- we may find open sets V, W separating x from K \ U.
    -- Then K \ W is a compact neighborhood of x contained in U.
    let ⟨v, w, vo, wo, xv, kuw, vw⟩ :=
      compact_compact_separated is_compact_singleton (IsCompact.diff kc uo)
        (by
          rw [singleton_inter_eq_empty] <;> exact fun h => h.2 xu)
    have wn : wᶜ ∈ 𝓝 x := mem_nhds_iff.mpr ⟨v, subset_compl_iff_disjoint.mpr vw, vo, singleton_subset_iff.mp xv⟩
    ⟨k \ w, Filter.inter_mem kx wn, Subset.trans (diff_subset_comm.mp kuw) un, kc.diff wo⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) locally_compact_of_compact [T2Space α] [CompactSpace α] : LocallyCompactSpace α :=
  locally_compact_of_compact_nhds fun x => ⟨Univ, is_open_univ.mem_nhds trivialₓ, compact_univ⟩

/-- In a locally compact T₂ space, every point has an open neighborhood with compact closure -/
theorem exists_open_with_compact_closure [LocallyCompactSpace α] [T2Space α] (x : α) :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsCompact (Closure U) := by
  rcases exists_compact_mem_nhds x with ⟨K, hKc, hxK⟩
  rcases mem_nhds_iff.1 hxK with ⟨t, h1t, h2t, h3t⟩
  exact ⟨t, h2t, h3t, compact_closure_of_subset_compact hKc h1t⟩

/-- In a locally compact T₂ space, every compact set has an open neighborhood with compact closure.
-/
theorem exists_open_superset_and_is_compact_closure [LocallyCompactSpace α] [T2Space α] {K : Set α} (hK : IsCompact K) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ IsCompact (Closure V) := by
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩
  refine' ⟨Interior K', is_open_interior, hKK', compact_closure_of_subset_compact hK' interior_subset⟩

theorem is_preirreducible_iff_subsingleton [T2Space α] (S : Set α) : IsPreirreducible S ↔ Set.Subsingleton S := by
  constructor
  · intro h x hx y hy
    by_contra e
    obtain ⟨U, V, hU, hV, hxU, hyV, h'⟩ := t2_separation e
    have := h U V hU hV ⟨x, hx, hxU⟩ ⟨y, hy, hyV⟩
    rw [h', inter_empty] at this
    exact this.some_spec
    
  · exact Set.Subsingleton.is_preirreducible
    

theorem is_irreducible_iff_singleton [T2Space α] (S : Set α) : IsIrreducible S ↔ ∃ x, S = {x} := by
  rw [IsIrreducible, is_preirreducible_iff_subsingleton, exists_eq_singleton_iff_nonempty_subsingleton]

end Separation

section Regularity

/-- A T₃ space, also known as a regular space (although this condition sometimes
  omits T₂), is one in which for every closed `C` and `x ∉ C`, there exist
  disjoint open sets containing `x` and `C` respectively. -/
class RegularSpace (α : Type u) [TopologicalSpace α] extends T0Space α : Prop where
  regular : ∀ {s : Set α} {a}, IsClosed s → a ∉ s → ∃ t, IsOpen t ∧ s ⊆ t ∧ 𝓝[t] a = ⊥

-- see Note [lower instance priority]
instance (priority := 100) RegularSpace.t1_space [RegularSpace α] : T1Space α := by
  rw [t1_space_iff_exists_open]
  intro x y hxy
  obtain ⟨U, hU, h⟩ := T0Space.t0 x y hxy
  cases h
  · exact ⟨U, hU, h⟩
    
  · obtain ⟨R, hR, hh⟩ := RegularSpace.regular (is_closed_compl_iff.mpr hU) (not_not.mpr h.1)
    obtain ⟨V, hV, hhh⟩ := mem_nhds_iff.1 (Filter.inf_principal_eq_bot.1 hh.2)
    exact ⟨R, hR, hh.1 (mem_compl h.2), hV hhh.2⟩
    

theorem nhds_is_closed [RegularSpace α] {a : α} {s : Set α} (h : s ∈ 𝓝 a) : ∃ t ∈ 𝓝 a, t ⊆ s ∧ IsClosed t :=
  let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_iff.mp h
  have : ∃ t, IsOpen t ∧ s'ᶜ ⊆ t ∧ 𝓝[t] a = ⊥ := RegularSpace.regular h₂.is_closed_compl (not_not_intro h₃)
  let ⟨t, ht₁, ht₂, ht₃⟩ := this
  ⟨tᶜ,
    mem_of_eq_bot <| by
      rwa [compl_compl],
    Subset.trans (compl_subset_comm.1 ht₂) h₁, is_closed_compl_iff.mpr ht₁⟩

theorem closed_nhds_basis [RegularSpace α] (a : α) : (𝓝 a).HasBasis (fun s : Set α => s ∈ 𝓝 a ∧ IsClosed s) id :=
  ⟨fun t =>
    ⟨fun t_in =>
      let ⟨s, s_in, h_st, h⟩ := nhds_is_closed t_in
      ⟨s, ⟨s_in, h⟩, h_st⟩,
      fun ⟨s, ⟨s_in, hs⟩, hst⟩ => mem_of_superset s_in hst⟩⟩

theorem TopologicalSpace.IsTopologicalBasis.exists_closure_subset [RegularSpace α] {B : Set (Set α)}
    (hB : TopologicalSpace.IsTopologicalBasis B) {a : α} {s : Set α} (h : s ∈ 𝓝 a) : ∃ t ∈ B, a ∈ t ∧ Closure t ⊆ s :=
  by
  rcases nhds_is_closed h with ⟨t, hat, hts, htc⟩
  rcases hB.mem_nhds_iff.1 hat with ⟨u, huB, hau, hut⟩
  exact ⟨u, huB, hau, (closure_minimal hut htc).trans hts⟩

theorem TopologicalSpace.IsTopologicalBasis.nhds_basis_closure [RegularSpace α] {B : Set (Set α)}
    (hB : TopologicalSpace.IsTopologicalBasis B) (a : α) : (𝓝 a).HasBasis (fun s : Set α => a ∈ s ∧ s ∈ B) Closure :=
  ⟨fun s =>
    ⟨fun h =>
      let ⟨t, htB, hat, hts⟩ := hB.exists_closure_subset h
      ⟨t, ⟨hat, htB⟩, hts⟩,
      fun ⟨t, ⟨hat, htB⟩, hts⟩ => mem_of_superset (hB.mem_nhds htB hat) (subset_closure.trans hts)⟩⟩

protected theorem Embedding.regular_space [TopologicalSpace β] [RegularSpace β] {f : α → β} (hf : Embedding f) :
    RegularSpace α :=
  { to_t0_space := hf.T0Space,
    regular := by
      intro s a hs ha
      rcases hf.to_inducing.is_closed_iff.1 hs with ⟨s, hs', rfl⟩
      rcases RegularSpace.regular hs' ha with ⟨t, ht, hst, hat⟩
      refine' ⟨f ⁻¹' t, ht.preimage hf.continuous, preimage_mono hst, _⟩
      rw [nhdsWithin, hf.to_inducing.nhds_eq_comap, ← comap_principal, ← comap_inf, ← nhdsWithin, hat, comap_bot] }

instance Subtype.regular_space [RegularSpace α] {p : α → Prop} : RegularSpace (Subtype p) :=
  embedding_subtype_coe.RegularSpace

variable (α)

-- see Note [lower instance priority]
instance (priority := 100) RegularSpace.t2_space [RegularSpace α] : T2Space α :=
  ⟨fun x y hxy =>
    let ⟨s, hs, hys, hxs⟩ := RegularSpace.regular is_closed_singleton (mt mem_singleton_iff.1 hxy)
    let ⟨t, hxt, u, hsu, htu⟩ := empty_mem_iff_bot.2 hxs
    let ⟨v, hvt, hv, hxv⟩ := mem_nhds_iff.1 hxt
    ⟨v, s, hv, hs, hxv, singleton_subset_iff.1 hys,
      eq_empty_of_subset_empty fun z ⟨hzv, hzs⟩ => by
        rw [htu]
        exact ⟨hvt hzv, hsu hzs⟩⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) RegularSpace.t2_5_space [RegularSpace α] : T25Space α :=
  ⟨fun x y hxy =>
    let ⟨U, V, hU, hV, hh_1, hh_2, hUV⟩ := T2Space.t2 x y hxy
    let hxcV := not_not.mpr ((interior_maximal (subset_compl_iff_disjoint.mpr hUV) hU) hh_1)
    let ⟨R, hR, hh⟩ :=
      RegularSpace.regular is_closed_closure
        (by
          rwa [closure_eq_compl_interior_compl])
    let ⟨A, hA, hhh⟩ := mem_nhds_iff.1 (Filter.inf_principal_eq_bot.1 hh.2)
    ⟨A, V, hhh.1, hV,
      subset_eq_empty
        ((Closure V).inter_subset_inter_left
          (Subset.trans (closure_minimal hA (is_closed_compl_iff.mpr hR)) (compl_subset_compl.mpr hh.1)))
        (compl_inter_self (Closure V)),
      hhh.2, hh_2⟩⟩

variable {α}

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (U₁ V₁ «expr ∈ » expr𝓝() x)
-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (U₂ V₂ «expr ∈ » expr𝓝() y)
/-- Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`,
with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint. -/
theorem disjoint_nested_nhds [RegularSpace α] {x y : α} (h : x ≠ y) :
    ∃ (U₁ V₁ : _)(_ : U₁ ∈ 𝓝 x)(_ : V₁ ∈ 𝓝 x)(U₂ V₂ : _)(_ : U₂ ∈ 𝓝 y)(_ : V₂ ∈ 𝓝 y),
      IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ U₁ ∩ U₂ = ∅ :=
  by
  rcases t2_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩
  rcases nhds_is_closed (IsOpen.mem_nhds U₁_op x_in) with ⟨V₁, V₁_in, h₁, V₁_closed⟩
  rcases nhds_is_closed (IsOpen.mem_nhds U₂_op y_in) with ⟨V₂, V₂_in, h₂, V₂_closed⟩
  use U₁, mem_of_superset V₁_in h₁, V₁, V₁_in, U₂, mem_of_superset V₂_in h₂, V₂, V₂_in
  tauto

/-- In a locally compact regular space, given a compact set `K` inside an open set `U`, we can find a
compact set `K'` between these sets: `K` is inside the interior of `K'` and `K' ⊆ U`.
-/
theorem exists_compact_between [LocallyCompactSpace α] [RegularSpace α] {K U : Set α} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ K', IsCompact K' ∧ K ⊆ Interior K' ∧ K' ⊆ U := by
  choose C hxC hCU hC using fun x : K => nhds_is_closed (hU.mem_nhds <| hKU x.2)
  choose L hL hxL using fun x : K => exists_compact_mem_nhds (x : α)
  have : K ⊆ ⋃ x, Interior (L x) ∩ Interior (C x) := fun x hx =>
    mem_Union.mpr ⟨⟨x, hx⟩, ⟨mem_interior_iff_mem_nhds.mpr (hxL _), mem_interior_iff_mem_nhds.mpr (hxC _)⟩⟩
  rcases hK.elim_finite_subcover _ _ this with ⟨t, ht⟩
  · refine' ⟨⋃ x ∈ t, L x ∩ C x, t.compact_bUnion fun x _ => (hL x).inter_right (hC x), fun x hx => _, _⟩
    · obtain ⟨y, hyt, hy : x ∈ Interior (L y) ∩ Interior (C y)⟩ := mem_Union₂.mp (ht hx)
      rw [← interior_inter] at hy
      refine' interior_mono (subset_bUnion_of_mem hyt) hy
      
    · simp_rw [Union_subset_iff]
      rintro x -
      exact (inter_subset_right _ _).trans (hCU _)
      
    
  · exact fun _ => is_open_interior.inter is_open_interior
    

/-- In a locally compact regular space, given a compact set `K` inside an open set `U`, we can find a
open set `V` between these sets with compact closure: `K ⊆ V` and the closure of `V` is inside `U`.
-/
theorem exists_open_between_and_is_compact_closure [LocallyCompactSpace α] [RegularSpace α] {K U : Set α}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) : ∃ V, IsOpen V ∧ K ⊆ V ∧ Closure V ⊆ U ∧ IsCompact (Closure V) :=
  by
  rcases exists_compact_between hK hU hKU with ⟨V, hV, hKV, hVU⟩
  refine'
    ⟨Interior V, is_open_interior, hKV, (closure_minimal interior_subset hV.is_closed).trans hVU,
      compact_closure_of_subset_compact hV interior_subset⟩

end Regularity

section Normality

/-- A T₄ space, also known as a normal space (although this condition sometimes
  omits T₂), is one in which for every pair of disjoint closed sets `C` and `D`,
  there exist disjoint open sets containing `C` and `D` respectively. -/
class NormalSpace (α : Type u) [TopologicalSpace α] extends T1Space α : Prop where
  normal :
    ∀ s t : Set α, IsClosed s → IsClosed t → Disjoint s t → ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v

theorem normal_separation [NormalSpace α] {s t : Set α} (H1 : IsClosed s) (H2 : IsClosed t) (H3 : Disjoint s t) :
    ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v :=
  NormalSpace.normal s t H1 H2 H3

theorem normal_exists_closure_subset [NormalSpace α] {s t : Set α} (hs : IsClosed s) (ht : IsOpen t) (hst : s ⊆ t) :
    ∃ u, IsOpen u ∧ s ⊆ u ∧ Closure u ⊆ t := by
  have : Disjoint s (tᶜ) := fun x ⟨hxs, hxt⟩ => hxt (hst hxs)
  rcases normal_separation hs (is_closed_compl_iff.2 ht) this with ⟨s', t', hs', ht', hss', htt', hs't'⟩
  refine' ⟨s', hs', hss', subset.trans (closure_minimal _ (is_closed_compl_iff.2 ht')) (compl_subset_comm.1 htt')⟩
  exact fun x hxs hxt => hs't' ⟨hxs, hxt⟩

-- see Note [lower instance priority]
instance (priority := 100) NormalSpace.regular_space [NormalSpace α] : RegularSpace α where
  regular := fun s x hs hxs =>
    let ⟨u, v, hu, hv, hsu, hxv, huv⟩ :=
      normal_separation hs is_closed_singleton fun _ ⟨hx, hy⟩ =>
        hxs <| mem_of_eq_of_mem (eq_of_mem_singleton hy).symm hx
    ⟨u, hu, hsu,
      Filter.empty_mem_iff_bot.1 <|
        Filter.mem_inf_iff.2
          ⟨v, IsOpen.mem_nhds hv (singleton_subset_iff.1 hxv), u, Filter.mem_principal_self u, by
            rwa [eq_comm, inter_comm, ← disjoint_iff_inter_eq_empty]⟩⟩

-- We can't make this an instance because it could cause an instance loop.
theorem normal_of_compact_t2 [CompactSpace α] [T2Space α] : NormalSpace α := by
  refine' ⟨fun s t hs ht st => _⟩
  simp only [disjoint_iff]
  exact compact_compact_separated hs.is_compact ht.is_compact st.eq_bot

protected theorem ClosedEmbedding.normal_space [TopologicalSpace β] [NormalSpace β] {f : α → β}
    (hf : ClosedEmbedding f) : NormalSpace α :=
  { to_t1_space := hf.toEmbedding.T1Space,
    normal := by
      intro s t hs ht hst
      rcases NormalSpace.normal (f '' s) (f '' t) (hf.is_closed_map s hs) (hf.is_closed_map t ht)
          (disjoint_image_of_injective hf.inj hst) with
        ⟨u, v, hu, hv, hsu, htv, huv⟩
      rw [image_subset_iff] at hsu htv
      exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hf.continuous, hv.preimage hf.continuous, hsu, htv, huv.preimage f⟩ }

variable (α)

/-- A regular topological space with second countable topology is a normal space.
This lemma is not an instance to avoid a loop. -/
theorem normal_space_of_regular_second_countable [SecondCountableTopology α] [RegularSpace α] : NormalSpace α := by
  have key :
    ∀ {s t : Set α},
      IsClosed t →
        Disjoint s t →
          ∃ U : Set (countable_basis α),
            (s ⊆ ⋃ u ∈ U, ↑u) ∧
              (∀, ∀ u ∈ U, ∀, Disjoint (Closure ↑u) t) ∧
                ∀ n : ℕ, IsClosed (⋃ (u ∈ U) (h : Encodable.encode u ≤ n), Closure (u : Set α)) :=
    by
    intro s t hc hd
    rw [disjoint_left] at hd
    have : ∀, ∀ x ∈ s, ∀, ∃ U ∈ countable_basis α, x ∈ U ∧ Disjoint (Closure U) t := by
      intro x hx
      rcases(is_basis_countable_basis α).exists_closure_subset (hc.is_open_compl.mem_nhds (hd hx)) with
        ⟨u, hu, hxu, hut⟩
      exact ⟨u, hu, hxu, disjoint_left.2 hut⟩
    choose! U hu hxu hd
    set V : s → countable_basis α := maps_to.restrict _ _ _ hu
    refine' ⟨range V, _, forall_range_iff.2 <| Subtype.forall.2 hd, fun n => _⟩
    · rw [bUnion_range]
      exact fun x hx => mem_Union.2 ⟨⟨x, hx⟩, hxu x hx⟩
      
    · simp only [← supr_eq_Union, supr_and']
      exact
        is_closed_bUnion (((finite_le_nat n).preimage_embedding (Encodable.encode' _)).Subset <| inter_subset_right _ _)
          fun u hu => is_closed_closure
      
  refine' ⟨fun s t hs ht hd => _⟩
  rcases key ht hd with ⟨U, hsU, hUd, hUc⟩
  rcases key hs hd.symm with ⟨V, htV, hVd, hVc⟩
  refine'
    ⟨⋃ u ∈ U, ↑u \ ⋃ (v ∈ V) (hv : Encodable.encode v ≤ Encodable.encode u), Closure ↑v,
      ⋃ v ∈ V, ↑v \ ⋃ (u ∈ U) (hu : Encodable.encode u ≤ Encodable.encode v), Closure ↑u,
      is_open_bUnion fun u hu => (is_open_of_mem_countable_basis u.2).sdiff (hVc _),
      is_open_bUnion fun v hv => (is_open_of_mem_countable_basis v.2).sdiff (hUc _), fun x hx => _, fun x hx => _, _⟩
  · rcases mem_Union₂.1 (hsU hx) with ⟨u, huU, hxu⟩
    refine' mem_bUnion huU ⟨hxu, _⟩
    simp only [mem_Union]
    rintro ⟨v, hvV, -, hxv⟩
    exact hVd v hvV ⟨hxv, hx⟩
    
  · rcases mem_Union₂.1 (htV hx) with ⟨v, hvV, hxv⟩
    refine' mem_bUnion hvV ⟨hxv, _⟩
    simp only [mem_Union]
    rintro ⟨u, huU, -, hxu⟩
    exact hUd u huU ⟨hxu, hx⟩
    
  · simp only [disjoint_left, mem_Union, mem_diff, not_exists, not_and, not_forall, not_not]
    rintro a ⟨u, huU, hau, haV⟩ v hvV hav
    cases' le_totalₓ (Encodable.encode u) (Encodable.encode v) with hle hle
    exacts[⟨u, huU, hle, subset_closure hau⟩, (haV _ hvV hle <| subset_closure hav).elim]
    

end Normality

/-- In a compact t2 space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
theorem connected_component_eq_Inter_clopen [T2Space α] [CompactSpace α] (x : α) :
    ConnectedComponent x = ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z := by
  apply eq_of_subset_of_subset connected_component_subset_Inter_clopen
  -- Reduce to showing that the clopen intersection is connected.
  refine' IsPreconnected.subset_connected_component _ (mem_Inter.2 fun Z => Z.2.2)
  -- We do this by showing that any disjoint cover by two closed sets implies
  -- that one of these closed sets must contain our whole thing.
  -- To reduce to the case where the cover is disjoint on all of `α` we need that `s` is closed
  have hs : @IsClosed _ _inst_1 (⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z) := is_closed_Inter fun Z => Z.2.1.2
  rw [is_preconnected_iff_subset_of_fully_disjoint_closed hs]
  intro a b ha hb hab ab_empty
  have := @normal_of_compact_t2 α _ _ _
  -- Since our space is normal, we get two larger disjoint open sets containing the disjoint
  -- closed sets. If we can show that our intersection is a subset of any of these we can then
  -- "descend" this to show that it is a subset of either a or b.
  rcases normal_separation ha hb (disjoint_iff.2 ab_empty) with ⟨u, v, hu, hv, hau, hbv, huv⟩
  -- If we can find a clopen set around x, contained in u ∪ v, we get a disjoint decomposition
  -- Z = Z ∩ u ∪ Z ∩ v of clopen sets. The intersection of all clopen neighbourhoods will then lie
  -- in whichever of u or v x lies in and hence will be a subset of either a or b.
  suffices ∃ Z : Set α, IsClopen Z ∧ x ∈ Z ∧ Z ⊆ u ∪ v by
    cases' this with Z H
    rw [disjoint_iff_inter_eq_empty] at huv
    have H1 := is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv
    rw [union_comm] at H
    have H2 := is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu (inter_comm u v ▸ huv)
    by_cases' x ∈ u
    -- The x ∈ u case.
    · left
      suffices (⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, ↑Z) ⊆ u by
        rw [← Set.disjoint_iff_inter_eq_empty] at huv
        replace hab : (⋂ Z : { Z // IsClopen Z ∧ x ∈ Z }, ↑Z) ≤ a ∪ b := hab
        replace this : (⋂ Z : { Z // IsClopen Z ∧ x ∈ Z }, ↑Z) ≤ u := this
        exact Disjoint.left_le_of_le_sup_right hab (huv.mono this hbv)
      · apply subset.trans _ (inter_subset_right Z u)
        apply Inter_subset (fun Z : { Z : Set α // IsClopen Z ∧ x ∈ Z } => ↑Z) ⟨Z ∩ u, H1, mem_inter H.2.1 h⟩
        
      
    -- If x ∉ u, we get x ∈ v since x ∈ u ∪ v. The rest is then like the x ∈ u case.
    have h1 : x ∈ v := by
      cases'
        (mem_union x u v).1
          (mem_of_subset_of_mem (subset.trans hab (union_subset_union hau hbv)) (mem_Inter.2 fun i => i.2.2)) with
        h1 h1
      · exfalso
        exact h h1
        
      · exact h1
        
    right
    suffices (⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, ↑Z) ⊆ v by
      rw [inter_comm, ← Set.disjoint_iff_inter_eq_empty] at huv
      replace hab : (⋂ Z : { Z // IsClopen Z ∧ x ∈ Z }, ↑Z) ≤ a ∪ b := hab
      replace this : (⋂ Z : { Z // IsClopen Z ∧ x ∈ Z }, ↑Z) ≤ v := this
      exact Disjoint.left_le_of_le_sup_left hab (huv.mono this hau)
    · apply subset.trans _ (inter_subset_right Z v)
      apply Inter_subset (fun Z : { Z : Set α // IsClopen Z ∧ x ∈ Z } => ↑Z) ⟨Z ∩ v, H2, mem_inter H.2.1 h1⟩
      
  -- Now we find the required Z. We utilize the fact that X \ u ∪ v will be compact,
  -- so there must be some finite intersection of clopen neighbourhoods of X disjoint to it,
  -- but a finite intersection of clopen sets is clopen so we let this be our Z.
  have H1 :=
    (is_closed_compl_iff.2 (hu.union hv)).IsCompact.inter_Inter_nonempty
      (fun Z : { Z : Set α // IsClopen Z ∧ x ∈ Z } => Z) fun Z => Z.2.1.2
  rw [← not_imp_not, not_forall, not_nonempty_iff_eq_empty, inter_comm] at H1
  have huv_union := subset.trans hab (union_subset_union hau hbv)
  rw [← compl_compl (u ∪ v), subset_compl_iff_disjoint] at huv_union
  cases' H1 huv_union with Zi H2
  refine' ⟨⋂ U ∈ Zi, Subtype.val U, _, _, _⟩
  · exact is_clopen_bInter fun Z hZ => Z.2.1
    
  · exact mem_Inter₂.2 fun Z hZ => Z.2.2
    
  · rwa [not_nonempty_iff_eq_empty, inter_comm, ← subset_compl_iff_disjoint, compl_compl] at H2
    

section Profinite

variable [T2Space α]

/-- A Hausdorff space with a clopen basis is totally separated. -/
theorem tot_sep_of_zero_dim (h : IsTopologicalBasis { s : Set α | IsClopen s }) : TotallySeparatedSpace α := by
  constructor
  rintro x - y - hxy
  obtain ⟨u, v, hu, hv, xu, yv, disj⟩ := t2_separation hxy
  obtain ⟨w, hw : IsClopen w, xw, wu⟩ := (is_topological_basis.mem_nhds_iff h).1 (IsOpen.mem_nhds hu xu)
  refine' ⟨w, wᶜ, hw.1, (is_clopen_compl_iff.2 hw).1, xw, _, _, Set.inter_compl_self w⟩
  · intro h
    have : y ∈ u ∩ v := ⟨wu h, yv⟩
    rwa [disj] at this
    
  rw [Set.union_compl_self]

variable [CompactSpace α]

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
theorem compact_t2_tot_disc_iff_tot_sep : TotallyDisconnectedSpace α ↔ TotallySeparatedSpace α := by
  constructor
  · intro h
    constructor
    rintro x - y -
    contrapose!
    intro hyp
    suffices x ∈ ConnectedComponent y by
      simpa [totally_disconnected_space_iff_connected_component_singleton.1 h y, mem_singleton_iff]
    rw [connected_component_eq_Inter_clopen, mem_Inter]
    rintro ⟨w : Set α, hw : IsClopen w, hy : y ∈ w⟩
    by_contra hx
    simpa using hyp (wᶜ) w (is_open_compl_iff.mpr hw.2) hw.1 hx hy
    
  apply TotallySeparatedSpace.totally_disconnected_space

variable [TotallyDisconnectedSpace α]

theorem nhds_basis_clopen (x : α) : (𝓝 x).HasBasis (fun s : Set α => x ∈ s ∧ IsClopen s) id :=
  ⟨fun U => by
    constructor
    · have : ConnectedComponent x = {x} := totally_disconnected_space_iff_connected_component_singleton.mp ‹_› x
      rw [connected_component_eq_Inter_clopen] at this
      intro hU
      let N := { Z // IsClopen Z ∧ x ∈ Z }
      suffices ∃ Z : N, Z.val ⊆ U by
        rcases this with ⟨⟨s, hs, hs'⟩, hs''⟩
        exact ⟨s, ⟨hs', hs⟩, hs''⟩
      have : Nonempty N := ⟨⟨univ, is_clopen_univ, mem_univ x⟩⟩
      have hNcl : ∀ Z : N, IsClosed Z.val := fun Z => Z.property.1.2
      have hdir : Directed Superset fun Z : N => Z.val := by
        rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
        exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left s t, inter_subset_right s t⟩
      have h_nhd : ∀, ∀ y ∈ ⋂ Z : N, Z.val, ∀, U ∈ 𝓝 y := by
        intro y y_in
        erw [this, mem_singleton_iff] at y_in
        rwa [y_in]
      exact exists_subset_nhd_of_compact_space hdir hNcl h_nhd
      
    · rintro ⟨V, ⟨hxV, V_op, -⟩, hUV : V ⊆ U⟩
      rw [mem_nhds_iff]
      exact ⟨V, hUV, V_op, hxV⟩
      ⟩

theorem is_topological_basis_clopen : IsTopologicalBasis { s : Set α | IsClopen s } := by
  apply is_topological_basis_of_open_of_nhds fun hU : IsClopen U => hU.1
  intro x U hxU U_op
  have : U ∈ 𝓝 x := IsOpen.mem_nhds U_op hxU
  rcases(nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩
  use V
  tauto

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set.  -/
theorem compact_exists_clopen_in_open {x : α} {U : Set α} (is_open : IsOpen U) (memU : x ∈ U) :
    ∃ (V : Set α)(hV : IsClopen V), x ∈ V ∧ V ⊆ U :=
  (IsTopologicalBasis.mem_nhds_iff is_topological_basis_clopen).1 (IsOpen.mem_nhds memU)

end Profinite

section LocallyCompact

variable {H : Type _} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]

/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
theorem loc_compact_Haus_tot_disc_of_zero_dim [TotallyDisconnectedSpace H] :
    IsTopologicalBasis { s : Set H | IsClopen s } := by
  refine' is_topological_basis_of_open_of_nhds (fun u hu => hu.1) _
  rintro x U memU hU
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU
  obtain ⟨t, h, ht, xt⟩ := mem_interior.1 xs
  let u : Set s := (coe : s → H) ⁻¹' Interior s
  have u_open_in_s : IsOpen u := is_open_interior.preimage continuous_subtype_coe
  let X : s := ⟨x, h xt⟩
  have Xu : X ∈ u := xs
  have : CompactSpace s := is_compact_iff_compact_space.1 comp
  obtain ⟨V : Set s, clopen_in_s, Vx, V_sub⟩ := compact_exists_clopen_in_open u_open_in_s Xu
  have V_clopen : IsClopen ((coe : s → H) '' V) := by
    refine' ⟨_, comp.is_closed.closed_embedding_subtype_coe.closed_iff_image_closed.1 clopen_in_s.2⟩
    let v : Set u := (coe : u → s) ⁻¹' V
    have : (coe : u → H) = (coe : s → H) ∘ (coe : u → s) := rfl
    have f0 : Embedding (coe : u → H) := embedding_subtype_coe.comp embedding_subtype_coe
    have f1 : OpenEmbedding (coe : u → H) := by
      refine' ⟨f0, _⟩
      · have : Set.Range (coe : u → H) = Interior s := by
          rw [this, Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe]
          apply Set.inter_eq_self_of_subset_left interior_subset
        rw [this]
        apply is_open_interior
        
    have f2 : IsOpen v := clopen_in_s.1.Preimage continuous_subtype_coe
    have f3 : (coe : s → H) '' V = (coe : u → H) '' v := by
      rw [this, image_comp coe coe, Subtype.image_preimage_coe, inter_eq_self_of_subset_left V_sub]
    rw [f3]
    apply f1.is_open_map v f2
  refine'
    ⟨coe '' V, V_clopen, by
      simp [Vx, h xt], _⟩
  trans s
  · simp
    
  assumption

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
theorem loc_compact_t2_tot_disc_iff_tot_sep : TotallyDisconnectedSpace H ↔ TotallySeparatedSpace H := by
  constructor
  · intro h
    exact tot_sep_of_zero_dim loc_compact_Haus_tot_disc_of_zero_dim
    
  apply TotallySeparatedSpace.totally_disconnected_space

end LocallyCompact

/-- `connected_components α` is Hausdorff when `α` is Hausdorff and compact -/
instance ConnectedComponents.t2 [T2Space α] [CompactSpace α] : T2Space (ConnectedComponents α) := by
  -- Proof follows that of: https://stacks.math.columbia.edu/tag/0900
  -- Fix 2 distinct connected components, with points a and b
  refine' ⟨connected_components.surjective_coe.forall₂.2 fun a b ne => _⟩
  rw [ConnectedComponents.coe_ne_coe] at ne
  have h := connected_component_disjoint Ne
  -- write ↑b as the intersection of all clopen subsets containing it
  rw [connected_component_eq_Inter_clopen b, disjoint_iff_inter_eq_empty] at h
  -- Now we show that this can be reduced to some clopen containing `↑b` being disjoint to `↑a`
  obtain ⟨U, V, hU, ha, hb, rfl⟩ :
    ∃ (U : Set α)(V : Set (ConnectedComponents α)),
      IsClopen U ∧ ConnectedComponent a ∩ U = ∅ ∧ ConnectedComponent b ⊆ U ∧ coe ⁻¹' V = U :=
    by
    cases' is_closed_connected_component.is_compact.elim_finite_subfamily_closed _ _ h with fin_a ha
    swap
    · exact fun Z => Z.2.1.2
      
    -- This clopen and its complement will separate the connected components of `a` and `b`
    set U : Set α := ⋂ (i : { Z // IsClopen Z ∧ b ∈ Z }) (H : i ∈ fin_a), i
    have hU : IsClopen U := is_clopen_bInter fun i j => i.2.1
    exact
      ⟨U, coe '' U, hU, ha, subset_Inter₂ fun Z _ => Z.2.1.connected_component_subset Z.2.2,
        (connected_components_preimage_image U).symm ▸ hU.bUnion_connected_component_eq⟩
  rw [connected_components.quotient_map_coe.is_clopen_preimage] at hU
  refine' ⟨Vᶜ, V, hU.compl.is_open, hU.is_open, _, hb mem_connected_component, compl_inter_self _⟩
  exact fun h => flip Set.Nonempty.ne_empty ha ⟨a, mem_connected_component, h⟩

