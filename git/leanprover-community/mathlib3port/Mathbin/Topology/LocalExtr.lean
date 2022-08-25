/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Order.Filter.Extr
import Mathbin.Topology.ContinuousOn

/-!
# Local extrema of functions on topological spaces

## Main definitions

This file defines special versions of `is_*_filter f a l`, `*=min/max/extr`,
from `order/filter/extr` for two kinds of filters: `nhds_within` and `nhds`.
These versions are called `is_local_*_on` and `is_local_*`, respectively.

## Main statements

Many lemmas in this file restate those from `order/filter/extr`, and you can find
a detailed documentation there. These convenience lemmas are provided only to make the dot notation
return propositions of expected types, not just `is_*_filter`.

Here is the list of statements specific to these two types of filters:

* `is_local_*.on`, `is_local_*_on.on_subset`: restrict to a subset;
* `is_local_*_on.inter` : intersect the set with another one;
* `is_*_on.localize` : a global extremum is a local extremum too.
* `is_[local_]*_on.is_local_*` : if we have `is_local_*_on f s a` and `s ∈ 𝓝 a`,
  then we have `is_local_* f a`.

-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [TopologicalSpace α]

open Set Filter

open TopologicalSpace Filter

section Preorderₓ

variable [Preorderₓ β] [Preorderₓ γ] (f : α → β) (s : Set α) (a : α)

/-- `is_local_min_on f s a` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMinOn :=
  IsMinFilter f (𝓝[s] a) a

/-- `is_local_max_on f s a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMaxOn :=
  IsMaxFilter f (𝓝[s] a) a

/-- `is_local_extr_on f s a` means `is_local_min_on f s a ∨ is_local_max_on f s a`. -/
def IsLocalExtrOn :=
  IsExtrFilter f (𝓝[s] a) a

/-- `is_local_min f a` means that `f a ≤ f x` for all `x` in some neighborhood of `a`. -/
def IsLocalMin :=
  IsMinFilter f (𝓝 a) a

/-- `is_local_max f a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def IsLocalMax :=
  IsMaxFilter f (𝓝 a) a

/-- `is_local_extr_on f s a` means `is_local_min_on f s a ∨ is_local_max_on f s a`. -/
def IsLocalExtr :=
  IsExtrFilter f (𝓝 a) a

variable {f s a}

theorem IsLocalExtrOn.elim {p : Prop} : IsLocalExtrOn f s a → (IsLocalMinOn f s a → p) → (IsLocalMaxOn f s a → p) → p :=
  Or.elim

theorem IsLocalExtr.elim {p : Prop} : IsLocalExtr f a → (IsLocalMin f a → p) → (IsLocalMax f a → p) → p :=
  Or.elim

/-! ### Restriction to (sub)sets -/


theorem IsLocalMin.on (h : IsLocalMin f a) (s) : IsLocalMinOn f s a :=
  h.filter_inf _

theorem IsLocalMax.on (h : IsLocalMax f a) (s) : IsLocalMaxOn f s a :=
  h.filter_inf _

theorem IsLocalExtr.on (h : IsLocalExtr f a) (s) : IsLocalExtrOn f s a :=
  h.filter_inf _

theorem IsLocalMinOn.on_subset {t : Set α} (hf : IsLocalMinOn f t a) (h : s ⊆ t) : IsLocalMinOn f s a :=
  hf.filter_mono <| nhds_within_mono a h

theorem IsLocalMaxOn.on_subset {t : Set α} (hf : IsLocalMaxOn f t a) (h : s ⊆ t) : IsLocalMaxOn f s a :=
  hf.filter_mono <| nhds_within_mono a h

theorem IsLocalExtrOn.on_subset {t : Set α} (hf : IsLocalExtrOn f t a) (h : s ⊆ t) : IsLocalExtrOn f s a :=
  hf.filter_mono <| nhds_within_mono a h

theorem IsLocalMinOn.inter (hf : IsLocalMinOn f s a) (t) : IsLocalMinOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)

theorem IsLocalMaxOn.inter (hf : IsLocalMaxOn f s a) (t) : IsLocalMaxOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)

theorem IsLocalExtrOn.inter (hf : IsLocalExtrOn f s a) (t) : IsLocalExtrOn f (s ∩ t) a :=
  hf.on_subset (inter_subset_left s t)

theorem IsMinOn.localize (hf : IsMinOn f s a) : IsLocalMinOn f s a :=
  hf.filter_mono <| inf_le_right

theorem IsMaxOn.localize (hf : IsMaxOn f s a) : IsLocalMaxOn f s a :=
  hf.filter_mono <| inf_le_right

theorem IsExtrOn.localize (hf : IsExtrOn f s a) : IsLocalExtrOn f s a :=
  hf.filter_mono <| inf_le_right

theorem IsLocalMinOn.is_local_min (hf : IsLocalMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a :=
  have : 𝓝 a ≤ 𝓟 s := le_principal_iff.2 hs
  hf.filter_mono <| le_inf le_rflₓ this

theorem IsLocalMaxOn.is_local_max (hf : IsLocalMaxOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMax f a :=
  have : 𝓝 a ≤ 𝓟 s := le_principal_iff.2 hs
  hf.filter_mono <| le_inf le_rflₓ this

theorem IsLocalExtrOn.is_local_extr (hf : IsLocalExtrOn f s a) (hs : s ∈ 𝓝 a) : IsLocalExtr f a :=
  hf.elim (fun hf => (hf.IsLocalMin hs).is_extr) fun hf => (hf.IsLocalMax hs).is_extr

theorem IsMinOn.is_local_min (hf : IsMinOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMin f a :=
  hf.localize.IsLocalMin hs

theorem IsMaxOn.is_local_max (hf : IsMaxOn f s a) (hs : s ∈ 𝓝 a) : IsLocalMax f a :=
  hf.localize.IsLocalMax hs

theorem IsExtrOn.is_local_extr (hf : IsExtrOn f s a) (hs : s ∈ 𝓝 a) : IsLocalExtr f a :=
  hf.localize.IsLocalExtr hs

theorem IsLocalMinOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMinOn f s a) [NeBot (𝓝[<] f a)] :
    ¬𝓝 (f a) ≤ map f (𝓝[s] a) := fun hle =>
  have : ∀ᶠ y in 𝓝[<] f a, f a ≤ y := (eventually_map.2 hf).filter_mono (inf_le_left.trans hle)
  let ⟨y, hy⟩ := (this.And self_mem_nhds_within).exists
  hy.1.not_lt hy.2

theorem IsLocalMaxOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalMaxOn f s a) [NeBot (𝓝[>] f a)] :
    ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
  @IsLocalMinOn.not_nhds_le_map α βᵒᵈ _ _ _ _ _ ‹_› hf ‹_›

theorem IsLocalExtrOn.not_nhds_le_map [TopologicalSpace β] (hf : IsLocalExtrOn f s a) [NeBot (𝓝[<] f a)]
    [NeBot (𝓝[>] f a)] : ¬𝓝 (f a) ≤ map f (𝓝[s] a) :=
  hf.elim (fun h => h.not_nhds_le_map) fun h => h.not_nhds_le_map

/-! ### Constant -/


theorem is_local_min_on_const {b : β} : IsLocalMinOn (fun _ => b) s a :=
  is_min_filter_const

theorem is_local_max_on_const {b : β} : IsLocalMaxOn (fun _ => b) s a :=
  is_max_filter_const

theorem is_local_extr_on_const {b : β} : IsLocalExtrOn (fun _ => b) s a :=
  is_extr_filter_const

theorem is_local_min_const {b : β} : IsLocalMin (fun _ => b) a :=
  is_min_filter_const

theorem is_local_max_const {b : β} : IsLocalMax (fun _ => b) a :=
  is_max_filter_const

theorem is_local_extr_const {b : β} : IsLocalExtr (fun _ => b) a :=
  is_extr_filter_const

/-! ### Composition with (anti)monotone functions -/


theorem IsLocalMin.comp_mono (hf : IsLocalMin f a) {g : β → γ} (hg : Monotone g) : IsLocalMin (g ∘ f) a :=
  hf.comp_mono hg

theorem IsLocalMax.comp_mono (hf : IsLocalMax f a) {g : β → γ} (hg : Monotone g) : IsLocalMax (g ∘ f) a :=
  hf.comp_mono hg

theorem IsLocalExtr.comp_mono (hf : IsLocalExtr f a) {g : β → γ} (hg : Monotone g) : IsLocalExtr (g ∘ f) a :=
  hf.comp_mono hg

theorem IsLocalMin.comp_antitone (hf : IsLocalMin f a) {g : β → γ} (hg : Antitone g) : IsLocalMax (g ∘ f) a :=
  hf.comp_antitone hg

theorem IsLocalMax.comp_antitone (hf : IsLocalMax f a) {g : β → γ} (hg : Antitone g) : IsLocalMin (g ∘ f) a :=
  hf.comp_antitone hg

theorem IsLocalExtr.comp_antitone (hf : IsLocalExtr f a) {g : β → γ} (hg : Antitone g) : IsLocalExtr (g ∘ f) a :=
  hf.comp_antitone hg

theorem IsLocalMinOn.comp_mono (hf : IsLocalMinOn f s a) {g : β → γ} (hg : Monotone g) : IsLocalMinOn (g ∘ f) s a :=
  hf.comp_mono hg

theorem IsLocalMaxOn.comp_mono (hf : IsLocalMaxOn f s a) {g : β → γ} (hg : Monotone g) : IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_mono hg

theorem IsLocalExtrOn.comp_mono (hf : IsLocalExtrOn f s a) {g : β → γ} (hg : Monotone g) : IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_mono hg

theorem IsLocalMinOn.comp_antitone (hf : IsLocalMinOn f s a) {g : β → γ} (hg : Antitone g) : IsLocalMaxOn (g ∘ f) s a :=
  hf.comp_antitone hg

theorem IsLocalMaxOn.comp_antitone (hf : IsLocalMaxOn f s a) {g : β → γ} (hg : Antitone g) : IsLocalMinOn (g ∘ f) s a :=
  hf.comp_antitone hg

theorem IsLocalExtrOn.comp_antitone (hf : IsLocalExtrOn f s a) {g : β → γ} (hg : Antitone g) :
    IsLocalExtrOn (g ∘ f) s a :=
  hf.comp_antitone hg

theorem IsLocalMin.bicomp_mono [Preorderₓ δ] {op : β → γ → δ} (hop : ((· ≤ ·)⇒(· ≤ ·)⇒(· ≤ ·)) op op)
    (hf : IsLocalMin f a) {g : α → γ} (hg : IsLocalMin g a) : IsLocalMin (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg

theorem IsLocalMax.bicomp_mono [Preorderₓ δ] {op : β → γ → δ} (hop : ((· ≤ ·)⇒(· ≤ ·)⇒(· ≤ ·)) op op)
    (hf : IsLocalMax f a) {g : α → γ} (hg : IsLocalMax g a) : IsLocalMax (fun x => op (f x) (g x)) a :=
  hf.bicomp_mono hop hg

-- No `extr` version because we need `hf` and `hg` to be of the same kind
theorem IsLocalMinOn.bicomp_mono [Preorderₓ δ] {op : β → γ → δ} (hop : ((· ≤ ·)⇒(· ≤ ·)⇒(· ≤ ·)) op op)
    (hf : IsLocalMinOn f s a) {g : α → γ} (hg : IsLocalMinOn g s a) : IsLocalMinOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg

theorem IsLocalMaxOn.bicomp_mono [Preorderₓ δ] {op : β → γ → δ} (hop : ((· ≤ ·)⇒(· ≤ ·)⇒(· ≤ ·)) op op)
    (hf : IsLocalMaxOn f s a) {g : α → γ} (hg : IsLocalMaxOn g s a) : IsLocalMaxOn (fun x => op (f x) (g x)) s a :=
  hf.bicomp_mono hop hg

/-! ### Composition with `continuous_at` -/


theorem IsLocalMin.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ} (hf : IsLocalMin f (g b))
    (hg : ContinuousAt g b) : IsLocalMin (f ∘ g) b :=
  hg hf

theorem IsLocalMax.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ} (hf : IsLocalMax f (g b))
    (hg : ContinuousAt g b) : IsLocalMax (f ∘ g) b :=
  hg hf

theorem IsLocalExtr.comp_continuous [TopologicalSpace δ] {g : δ → α} {b : δ} (hf : IsLocalExtr f (g b))
    (hg : ContinuousAt g b) : IsLocalExtr (f ∘ g) b :=
  hf.comp_tendsto hg

theorem IsLocalMin.comp_continuous_on [TopologicalSpace δ] {s : Set δ} {g : δ → α} {b : δ} (hf : IsLocalMin f (g b))
    (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)

theorem IsLocalMax.comp_continuous_on [TopologicalSpace δ] {s : Set δ} {g : δ → α} {b : δ} (hf : IsLocalMax f (g b))
    (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto (hg b hb)

theorem IsLocalExtr.comp_continuous_on [TopologicalSpace δ] {s : Set δ} (g : δ → α) {b : δ} (hf : IsLocalExtr f (g b))
    (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuous_on hg hb).is_extr) fun hf => (IsLocalMax.comp_continuous_on hf hg hb).is_extr

theorem IsLocalMinOn.comp_continuous_on [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ → α} {b : δ}
    (hf : IsLocalMinOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMinOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhds_within_mono_right (image_subset_iff.mpr hst) (ContinuousWithinAt.tendsto_nhds_within_image (hg b hb)))

theorem IsLocalMaxOn.comp_continuous_on [TopologicalSpace δ] {t : Set α} {s : Set δ} {g : δ → α} {b : δ}
    (hf : IsLocalMaxOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) : IsLocalMaxOn (f ∘ g) s b :=
  hf.comp_tendsto
    (tendsto_nhds_within_mono_right (image_subset_iff.mpr hst) (ContinuousWithinAt.tendsto_nhds_within_image (hg b hb)))

theorem IsLocalExtrOn.comp_continuous_on [TopologicalSpace δ] {t : Set α} {s : Set δ} (g : δ → α) {b : δ}
    (hf : IsLocalExtrOn f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : ContinuousOn g s) (hb : b ∈ s) :
    IsLocalExtrOn (f ∘ g) s b :=
  hf.elim (fun hf => (hf.comp_continuous_on hst hg hb).is_extr) fun hf =>
    (IsLocalMaxOn.comp_continuous_on hf hst hg hb).is_extr

end Preorderₓ

/-! ### Pointwise addition -/


section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsLocalMin.add (hf : IsLocalMin f a) (hg : IsLocalMin g a) : IsLocalMin (fun x => f x + g x) a :=
  hf.add hg

theorem IsLocalMax.add (hf : IsLocalMax f a) (hg : IsLocalMax g a) : IsLocalMax (fun x => f x + g x) a :=
  hf.add hg

theorem IsLocalMinOn.add (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) : IsLocalMinOn (fun x => f x + g x) s a :=
  hf.add hg

theorem IsLocalMaxOn.add (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) : IsLocalMaxOn (fun x => f x + g x) s a :=
  hf.add hg

end OrderedAddCommMonoid

/-! ### Pointwise negation and subtraction -/


section OrderedAddCommGroup

variable [OrderedAddCommGroup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsLocalMin.neg (hf : IsLocalMin f a) : IsLocalMax (fun x => -f x) a :=
  hf.neg

theorem IsLocalMax.neg (hf : IsLocalMax f a) : IsLocalMin (fun x => -f x) a :=
  hf.neg

theorem IsLocalExtr.neg (hf : IsLocalExtr f a) : IsLocalExtr (fun x => -f x) a :=
  hf.neg

theorem IsLocalMinOn.neg (hf : IsLocalMinOn f s a) : IsLocalMaxOn (fun x => -f x) s a :=
  hf.neg

theorem IsLocalMaxOn.neg (hf : IsLocalMaxOn f s a) : IsLocalMinOn (fun x => -f x) s a :=
  hf.neg

theorem IsLocalExtrOn.neg (hf : IsLocalExtrOn f s a) : IsLocalExtrOn (fun x => -f x) s a :=
  hf.neg

theorem IsLocalMin.sub (hf : IsLocalMin f a) (hg : IsLocalMax g a) : IsLocalMin (fun x => f x - g x) a :=
  hf.sub hg

theorem IsLocalMax.sub (hf : IsLocalMax f a) (hg : IsLocalMin g a) : IsLocalMax (fun x => f x - g x) a :=
  hf.sub hg

theorem IsLocalMinOn.sub (hf : IsLocalMinOn f s a) (hg : IsLocalMaxOn g s a) : IsLocalMinOn (fun x => f x - g x) s a :=
  hf.sub hg

theorem IsLocalMaxOn.sub (hf : IsLocalMaxOn f s a) (hg : IsLocalMinOn g s a) : IsLocalMaxOn (fun x => f x - g x) s a :=
  hf.sub hg

end OrderedAddCommGroup

/-! ### Pointwise `sup`/`inf` -/


section SemilatticeSup

variable [SemilatticeSup β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsLocalMin.sup (hf : IsLocalMin f a) (hg : IsLocalMin g a) : IsLocalMin (fun x => f x⊔g x) a :=
  hf.sup hg

theorem IsLocalMax.sup (hf : IsLocalMax f a) (hg : IsLocalMax g a) : IsLocalMax (fun x => f x⊔g x) a :=
  hf.sup hg

theorem IsLocalMinOn.sup (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) : IsLocalMinOn (fun x => f x⊔g x) s a :=
  hf.sup hg

theorem IsLocalMaxOn.sup (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) : IsLocalMaxOn (fun x => f x⊔g x) s a :=
  hf.sup hg

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsLocalMin.inf (hf : IsLocalMin f a) (hg : IsLocalMin g a) : IsLocalMin (fun x => f x⊓g x) a :=
  hf.inf hg

theorem IsLocalMax.inf (hf : IsLocalMax f a) (hg : IsLocalMax g a) : IsLocalMax (fun x => f x⊓g x) a :=
  hf.inf hg

theorem IsLocalMinOn.inf (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) : IsLocalMinOn (fun x => f x⊓g x) s a :=
  hf.inf hg

theorem IsLocalMaxOn.inf (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) : IsLocalMaxOn (fun x => f x⊓g x) s a :=
  hf.inf hg

end SemilatticeInf

/-! ### Pointwise `min`/`max` -/


section LinearOrderₓ

variable [LinearOrderₓ β] {f g : α → β} {a : α} {s : Set α} {l : Filter α}

theorem IsLocalMin.min (hf : IsLocalMin f a) (hg : IsLocalMin g a) : IsLocalMin (fun x => min (f x) (g x)) a :=
  hf.min hg

theorem IsLocalMax.min (hf : IsLocalMax f a) (hg : IsLocalMax g a) : IsLocalMax (fun x => min (f x) (g x)) a :=
  hf.min hg

theorem IsLocalMinOn.min (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => min (f x) (g x)) s a :=
  hf.min hg

theorem IsLocalMaxOn.min (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => min (f x) (g x)) s a :=
  hf.min hg

theorem IsLocalMin.max (hf : IsLocalMin f a) (hg : IsLocalMin g a) : IsLocalMin (fun x => max (f x) (g x)) a :=
  hf.max hg

theorem IsLocalMax.max (hf : IsLocalMax f a) (hg : IsLocalMax g a) : IsLocalMax (fun x => max (f x) (g x)) a :=
  hf.max hg

theorem IsLocalMinOn.max (hf : IsLocalMinOn f s a) (hg : IsLocalMinOn g s a) :
    IsLocalMinOn (fun x => max (f x) (g x)) s a :=
  hf.max hg

theorem IsLocalMaxOn.max (hf : IsLocalMaxOn f s a) (hg : IsLocalMaxOn g s a) :
    IsLocalMaxOn (fun x => max (f x) (g x)) s a :=
  hf.max hg

end LinearOrderₓ

section Eventually

/-! ### Relation with `eventually` comparisons of two functions -/


variable [Preorderₓ β] {s : Set α}

theorem Filter.EventuallyLe.is_local_max_on {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝[s] a] f) (hfga : f a = g a)
    (h : IsLocalMaxOn f s a) : IsLocalMaxOn g s a :=
  hle.IsMaxFilter hfga h

theorem IsLocalMaxOn.congr {f g : α → β} {a : α} (h : IsLocalMaxOn f s a) (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) :
    IsLocalMaxOn g s a :=
  h.congr HEq <| HEq.eq_of_nhds_within hmem

theorem Filter.EventuallyEq.is_local_max_on_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) :
    IsLocalMaxOn f s a ↔ IsLocalMaxOn g s a :=
  HEq.is_max_filter_iff <| HEq.eq_of_nhds_within hmem

theorem Filter.EventuallyLe.is_local_min_on {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝[s] a] g) (hfga : f a = g a)
    (h : IsLocalMinOn f s a) : IsLocalMinOn g s a :=
  hle.IsMinFilter hfga h

theorem IsLocalMinOn.congr {f g : α → β} {a : α} (h : IsLocalMinOn f s a) (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) :
    IsLocalMinOn g s a :=
  h.congr HEq <| HEq.eq_of_nhds_within hmem

theorem Filter.EventuallyEq.is_local_min_on_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) :
    IsLocalMinOn f s a ↔ IsLocalMinOn g s a :=
  HEq.is_min_filter_iff <| HEq.eq_of_nhds_within hmem

theorem IsLocalExtrOn.congr {f g : α → β} {a : α} (h : IsLocalExtrOn f s a) (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) :
    IsLocalExtrOn g s a :=
  h.congr HEq <| HEq.eq_of_nhds_within hmem

theorem Filter.EventuallyEq.is_local_extr_on_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝[s] a] g) (hmem : a ∈ s) :
    IsLocalExtrOn f s a ↔ IsLocalExtrOn g s a :=
  HEq.is_extr_filter_iff <| HEq.eq_of_nhds_within hmem

theorem Filter.EventuallyLe.is_local_max {f g : α → β} {a : α} (hle : g ≤ᶠ[𝓝 a] f) (hfga : f a = g a)
    (h : IsLocalMax f a) : IsLocalMax g a :=
  hle.IsMaxFilter hfga h

theorem IsLocalMax.congr {f g : α → β} {a : α} (h : IsLocalMax f a) (heq : f =ᶠ[𝓝 a] g) : IsLocalMax g a :=
  h.congr HEq HEq.eq_of_nhds

theorem Filter.EventuallyEq.is_local_max_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMax f a ↔ IsLocalMax g a :=
  HEq.is_max_filter_iff HEq.eq_of_nhds

theorem Filter.EventuallyLe.is_local_min {f g : α → β} {a : α} (hle : f ≤ᶠ[𝓝 a] g) (hfga : f a = g a)
    (h : IsLocalMin f a) : IsLocalMin g a :=
  hle.IsMinFilter hfga h

theorem IsLocalMin.congr {f g : α → β} {a : α} (h : IsLocalMin f a) (heq : f =ᶠ[𝓝 a] g) : IsLocalMin g a :=
  h.congr HEq HEq.eq_of_nhds

theorem Filter.EventuallyEq.is_local_min_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalMin f a ↔ IsLocalMin g a :=
  HEq.is_min_filter_iff HEq.eq_of_nhds

theorem IsLocalExtr.congr {f g : α → β} {a : α} (h : IsLocalExtr f a) (heq : f =ᶠ[𝓝 a] g) : IsLocalExtr g a :=
  h.congr HEq HEq.eq_of_nhds

theorem Filter.EventuallyEq.is_local_extr_iff {f g : α → β} {a : α} (heq : f =ᶠ[𝓝 a] g) :
    IsLocalExtr f a ↔ IsLocalExtr g a :=
  HEq.is_extr_filter_iff HEq.eq_of_nhds

end Eventually

