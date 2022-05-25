/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
import Mathbin.Data.Set.Prod
import Mathbin.Logic.Function.Conjugate

/-!
# Functions over sets

## Main definitions

### Predicate

* `set.eq_on f₁ f₂ s` : functions `f₁` and `f₂` are equal at every point of `s`;
* `set.maps_to f s t` : `f` sends every point of `s` to a point of `t`;
* `set.inj_on f s` : restriction of `f` to `s` is injective;
* `set.surj_on f s t` : every point in `s` has a preimage in `s`;
* `set.bij_on f s t` : `f` is a bijection between `s` and `t`;
* `set.left_inv_on f' f s` : for every `x ∈ s` we have `f' (f x) = x`;
* `set.right_inv_on f' f t` : for every `y ∈ t` we have `f (f' y) = y`;
* `set.inv_on f' f s t` : `f'` is a two-side inverse of `f` on `s` and `t`, i.e.
  we have `set.left_inv_on f' f s` and `set.right_inv_on f' f t`.

### Functions

* `set.restrict f s` : restrict the domain of `f` to the set `s`;
* `set.cod_restrict f s h` : given `h : ∀ x, f x ∈ s`, restrict the codomain of `f` to the set `s`;
* `set.maps_to.restrict f s t h`: given `h : maps_to f s t`, restrict the domain of `f` to `s`
  and the codomain to `t`.
-/


universe u v w x y

variable {α : Type u} {β : Type v} {π : α → Type v} {γ : Type w} {ι : Sort x}

open Function

namespace Set

/-! ### Restrict -/


/-- Restrict domain of a function `f` to a set `s`. Same as `subtype.restrict` but this version
takes an argument `↥s` instead of `subtype s`. -/
def restrict (s : Set α) (f : ∀ a : α, π a) : ∀ a : s, π a := fun x => f x

theorem restrict_eq (f : α → β) (s : Set α) : s.restrict f = f ∘ coe :=
  rfl

@[simp]
theorem restrict_apply (f : α → β) (s : Set α) (x : s) : s.restrict f x = f x :=
  rfl

@[simp]
theorem range_restrict (f : α → β) (s : Set α) : Set.Range (s.restrict f) = f '' s :=
  (range_comp _ _).trans <| congr_argₓ ((· '' ·) f) Subtype.range_coe

theorem image_restrict (f : α → β) (s t : Set α) : s.restrict f '' (coe ⁻¹' t) = f '' (t ∩ s) := by
  rw [restrict, image_comp, image_preimage_eq_inter_range, Subtype.range_coe]

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (a «expr ∉ » s)
@[simp]
theorem restrict_dite {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀, ∀ a ∈ s, ∀, β) (g : ∀ a _ : a ∉ s, β) :
    (s.restrict fun a => if h : a ∈ s then f a h else g a h) = fun a => f a a.2 :=
  funext fun a => dif_pos a.2

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (a «expr ∉ » s)
@[simp]
theorem restrict_dite_compl {s : Set α} [∀ x, Decidable (x ∈ s)] (f : ∀, ∀ a ∈ s, ∀, β) (g : ∀ a _ : a ∉ s, β) :
    (sᶜ.restrict fun a => if h : a ∈ s then f a h else g a h) = fun a => g a a.2 :=
  funext fun a => dif_neg a.2

@[simp]
theorem restrict_ite (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (s.restrict fun a => if a ∈ s then f a else g a) = s.restrict f :=
  restrict_dite _ _

@[simp]
theorem restrict_ite_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    (sᶜ.restrict fun a => if a ∈ s then f a else g a) = sᶜ.restrict g :=
  restrict_dite_compl _ _

@[simp]
theorem restrict_piecewise (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    s.restrict (piecewise s f g) = s.restrict f :=
  restrict_ite _ _ _

@[simp]
theorem restrict_piecewise_compl (f g : α → β) (s : Set α) [∀ x, Decidable (x ∈ s)] :
    sᶜ.restrict (piecewise s f g) = sᶜ.restrict g :=
  restrict_ite_compl _ _ _

theorem restrict_extend_range (f : α → β) (g : α → γ) (g' : β → γ) :
    (Range f).restrict (extendₓ f g g') = fun x => g x.coe_prop.some := by
  convert restrict_dite _ _

@[simp]
theorem restrict_extend_compl_range (f : α → β) (g : α → γ) (g' : β → γ) :
    Range fᶜ.restrict (extendₓ f g g') = g' ∘ coe := by
  convert restrict_dite_compl _ _

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem range_extend_subset (f : α → β) (g : α → γ) (g' : β → γ) : Range (extendₓ f g g') ⊆ Range g ∪ g' '' Range fᶜ :=
  by
  classical
  rintro _ ⟨y, rfl⟩
  rw [extend_def]
  split_ifs
  exacts[Or.inl (mem_range_self _), Or.inr (mem_image_of_mem _ h)]

theorem range_extend {f : α → β} (hf : Injective f) (g : α → γ) (g' : β → γ) :
    Range (extendₓ f g g') = Range g ∪ g' '' Range fᶜ := by
  refine' (range_extend_subset _ _ _).antisymm _
  rintro z (⟨x, rfl⟩ | ⟨y, hy, rfl⟩)
  exacts[⟨f x, extend_apply hf _ _ _⟩, ⟨y, extend_apply' _ _ _ hy⟩]

/-- Restrict codomain of a function `f` to a set `s`. Same as `subtype.coind` but this version
has codomain `↥s` instead of `subtype s`. -/
def codRestrict (f : α → β) (s : Set β) (h : ∀ x, f x ∈ s) : α → s := fun x => ⟨f x, h x⟩

@[simp]
theorem coe_cod_restrict_apply (f : α → β) (s : Set β) (h : ∀ x, f x ∈ s) (x : α) : (codRestrict f s h x : β) = f x :=
  rfl

@[simp]
theorem restrict_comp_cod_restrict {f : α → β} {g : β → γ} {b : Set β} (h : ∀ x, f x ∈ b) :
    b.restrict g ∘ b.codRestrict f h = g ∘ f :=
  rfl

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {p : Set γ} {f f₁ f₂ f₃ : α → β} {g g₁ g₂ : β → γ} {f' f₁' f₂' : β → α}
  {g' : γ → β}

@[simp]
theorem injective_cod_restrict (h : ∀ x, f x ∈ t) : Injective (codRestrict f t h) ↔ Injective f := by
  simp only [injective, Subtype.ext_iff, coe_cod_restrict_apply]

alias injective_cod_restrict ↔ _ Function.Injective.cod_restrict

/-! ### Equality on a set -/


/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

@[simp]
theorem eq_on_empty (f₁ f₂ : α → β) : EqOn f₁ f₂ ∅ := fun x => False.elim

@[symm]
theorem EqOn.symm (h : EqOn f₁ f₂ s) : EqOn f₂ f₁ s := fun x hx => (h hx).symm

theorem eq_on_comm : EqOn f₁ f₂ s ↔ EqOn f₂ f₁ s :=
  ⟨EqOn.symm, EqOn.symm⟩

@[refl]
theorem eq_on_refl (f : α → β) (s : Set α) : EqOn f f s := fun _ _ => rfl

@[trans]
theorem EqOn.trans (h₁ : EqOn f₁ f₂ s) (h₂ : EqOn f₂ f₃ s) : EqOn f₁ f₃ s := fun x hx => (h₁ hx).trans (h₂ hx)

theorem EqOn.image_eq (heq : EqOn f₁ f₂ s) : f₁ '' s = f₂ '' s :=
  image_congr HEq

theorem EqOn.inter_preimage_eq (heq : EqOn f₁ f₂ s) (t : Set β) : s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t :=
  ext fun x =>
    And.congr_right_iff.2 fun hx => by
      rw [mem_preimage, mem_preimage, HEq hx]

theorem EqOn.mono (hs : s₁ ⊆ s₂) (hf : EqOn f₁ f₂ s₂) : EqOn f₁ f₂ s₁ := fun x hx => hf (hs hx)

theorem EqOn.comp_left (h : s.EqOn f₁ f₂) : s.EqOn (g ∘ f₁) (g ∘ f₂) := fun a ha => congr_argₓ _ <| h ha

theorem comp_eq_of_eq_on_range {ι : Sort _} {f : ι → α} {g₁ g₂ : α → β} (h : EqOn g₁ g₂ (Range f)) : g₁ ∘ f = g₂ ∘ f :=
  funext fun x => h <| mem_range_self _

/-! ### Congruence lemmas -/


section Order

variable [Preorderₓ α] [Preorderₓ β]

theorem _root_.monotone_on.congr (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂) : MonotoneOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab

theorem _root_.antitone_on.congr (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂) : AntitoneOn f₂ s :=
  h₁.dual_right.congr h

theorem _root_.strict_mono_on.congr (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂) : StrictMonoOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab

theorem _root_.strict_anti_on.congr (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂) : StrictAntiOn f₂ s :=
  h₁.dual_right.congr h

theorem EqOn.congr_monotone_on (h : s.EqOn f₁ f₂) : MonotoneOn f₁ s ↔ MonotoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

theorem EqOn.congr_antitone_on (h : s.EqOn f₁ f₂) : AntitoneOn f₁ s ↔ AntitoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

theorem EqOn.congr_strict_mono_on (h : s.EqOn f₁ f₂) : StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

theorem EqOn.congr_strict_anti_on (h : s.EqOn f₁ f₂) : StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

end Order

/-! ### Mono lemmas-/


section Mono

variable [Preorderₓ α] [Preorderₓ β]

theorem _root_.monotone_on.mono (h : MonotoneOn f s) (h' : s₂ ⊆ s) : MonotoneOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)

theorem _root_.antitone_on.mono (h : AntitoneOn f s) (h' : s₂ ⊆ s) : AntitoneOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)

theorem _root_.strict_mono_on.mono (h : StrictMonoOn f s) (h' : s₂ ⊆ s) : StrictMonoOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)

theorem _root_.strict_anti_on.mono (h : StrictAntiOn f s) (h' : s₂ ⊆ s) : StrictAntiOn f s₂ := fun x hx y hy =>
  h (h' hx) (h' hy)

end Mono

/-! ### maps to -/


/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f x ∈ t

/-- Given a map `f` sending `s : set α` into `t : set β`, restrict domain of `f` to `s`
and the codomain to `t`. Same as `subtype.map`. -/
def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  Subtype.map f h

@[simp]
theorem MapsTo.coe_restrict_apply (h : MapsTo f s t) (x : s) : (h.restrict f s t x : β) = f x :=
  rfl

theorem maps_to_iff_exists_map_subtype : MapsTo f s t ↔ ∃ g : s → t, ∀ x : s, f x = g x :=
  ⟨fun h => ⟨h.restrict f s t, fun _ => rfl⟩, fun x hx => by
    erw [hg ⟨x, hx⟩]
    apply Subtype.coe_prop⟩

theorem maps_to' : MapsTo f s t ↔ f '' s ⊆ t :=
  image_subset_iff.symm

@[simp]
theorem maps_to_singleton {x : α} : MapsTo f {x} t ↔ f x ∈ t :=
  singleton_subset_iff

theorem maps_to_empty (f : α → β) (t : Set β) : MapsTo f ∅ t :=
  empty_subset _

theorem MapsTo.image_subset (h : MapsTo f s t) : f '' s ⊆ t :=
  maps_to'.1 h

theorem MapsTo.congr (h₁ : MapsTo f₁ s t) (h : EqOn f₁ f₂ s) : MapsTo f₂ s t := fun x hx => h hx ▸ h₁ hx

theorem EqOn.comp_right (hg : t.EqOn g₁ g₂) (hf : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) := fun a ha => hg <| hf ha

theorem EqOn.maps_to_iff (H : EqOn f₁ f₂ s) : MapsTo f₁ s t ↔ MapsTo f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem MapsTo.comp (h₁ : MapsTo g t p) (h₂ : MapsTo f s t) : MapsTo (g ∘ f) s p := fun x h => h₁ (h₂ h)

theorem maps_to_id (s : Set α) : MapsTo id s s := fun x => id

theorem MapsTo.iterate {f : α → α} {s : Set α} (h : MapsTo f s s) : ∀ n, MapsTo (f^[n]) s s
  | 0 => fun _ => id
  | n + 1 => (maps_to.iterate n).comp h

theorem MapsTo.iterate_restrict {f : α → α} {s : Set α} (h : MapsTo f s s) (n : ℕ) :
    h.restrict f s s^[n] = (h.iterate n).restrict _ _ _ := by
  funext x
  rw [Subtype.ext_iff, maps_to.coe_restrict_apply]
  induction' n with n ihn generalizing x
  · rfl
    
  · simp [Nat.iterate, ihn]
    

theorem MapsTo.mono (hf : MapsTo f s₁ t₁) (hs : s₂ ⊆ s₁) (ht : t₁ ⊆ t₂) : MapsTo f s₂ t₂ := fun x hx => ht (hf <| hs hx)

theorem MapsTo.mono_left (hf : MapsTo f s₁ t) (hs : s₂ ⊆ s₁) : MapsTo f s₂ t := fun x hx => hf (hs hx)

theorem MapsTo.mono_right (hf : MapsTo f s t₁) (ht : t₁ ⊆ t₂) : MapsTo f s t₂ := fun x hx => ht (hf hx)

theorem MapsTo.union_union (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) : MapsTo f (s₁ ∪ s₂) (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => Or.inl <| h₁ hx) fun hx => Or.inr <| h₂ hx

theorem MapsTo.union (h₁ : MapsTo f s₁ t) (h₂ : MapsTo f s₂ t) : MapsTo f (s₁ ∪ s₂) t :=
  union_self t ▸ h₁.union_union h₂

@[simp]
theorem maps_to_union : MapsTo f (s₁ ∪ s₂) t ↔ MapsTo f s₁ t ∧ MapsTo f s₂ t :=
  ⟨fun h => ⟨h.mono (subset_union_left s₁ s₂) (Subset.refl t), h.mono (subset_union_right s₁ s₂) (Subset.refl t)⟩,
    fun h => h.1.union h.2⟩

theorem MapsTo.inter (h₁ : MapsTo f s t₁) (h₂ : MapsTo f s t₂) : MapsTo f s (t₁ ∩ t₂) := fun x hx => ⟨h₁ hx, h₂ hx⟩

theorem MapsTo.inter_inter (h₁ : MapsTo f s₁ t₁) (h₂ : MapsTo f s₂ t₂) : MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun x hx =>
  ⟨h₁ hx.1, h₂ hx.2⟩

@[simp]
theorem maps_to_inter : MapsTo f s (t₁ ∩ t₂) ↔ MapsTo f s t₁ ∧ MapsTo f s t₂ :=
  ⟨fun h => ⟨h.mono (Subset.refl s) (inter_subset_left t₁ t₂), h.mono (Subset.refl s) (inter_subset_right t₁ t₂)⟩,
    fun h => h.1.inter h.2⟩

theorem maps_to_univ (f : α → β) (s : Set α) : MapsTo f s Univ := fun x h => trivialₓ

theorem maps_to_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) := by
  rw [maps_to']

theorem maps_to_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t :=
  Subset.refl _

theorem maps_to_range (f : α → β) (s : Set α) : MapsTo f s (Range f) :=
  (maps_to_image f s).mono (Subset.refl s) (image_subset_range _ _)

@[simp]
theorem maps_image_to (f : α → β) (g : γ → α) (s : Set γ) (t : Set β) : MapsTo f (g '' s) t ↔ MapsTo (f ∘ g) s t :=
  ⟨fun h c hc => h ⟨c, hc, rfl⟩, fun h d ⟨c, hc⟩ => hc.2 ▸ h hc.1⟩

@[simp]
theorem maps_univ_to (f : α → β) (s : Set β) : MapsTo f Univ s ↔ ∀ a, f a ∈ s :=
  ⟨fun h a => h (mem_univ _), fun h x _ => h x⟩

@[simp]
theorem maps_range_to (f : α → β) (g : γ → α) (s : Set β) : MapsTo f (Range g) s ↔ MapsTo (f ∘ g) Univ s := by
  rw [← image_univ, maps_image_to]

theorem surjective_maps_to_image_restrict (f : α → β) (s : Set α) :
    Surjective ((maps_to_image f s).restrict f s (f '' s)) := fun ⟨y, x, hs, hxy⟩ => ⟨⟨x, hs⟩, Subtype.ext hxy⟩

theorem MapsTo.mem_iff (h : MapsTo f s t) (hc : MapsTo f (sᶜ) (tᶜ)) {x} : f x ∈ t ↔ x ∈ s :=
  ⟨fun ht => by_contra fun hs => hc hs ht, fun hx => h hx⟩

/-! ### Injectivity on a set -/


/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂

theorem Subsingleton.inj_on (hs : s.Subsingleton) (f : α → β) : InjOn f s := fun x hx y hy h => hs hx hy

@[simp]
theorem inj_on_empty (f : α → β) : InjOn f ∅ :=
  subsingleton_empty.InjOn f

@[simp]
theorem inj_on_singleton (f : α → β) (a : α) : InjOn f {a} :=
  subsingleton_singleton.InjOn f

theorem InjOn.eq_iff {x y} (h : InjOn f s) (hx : x ∈ s) (hy : y ∈ s) : f x = f y ↔ x = y :=
  ⟨h hx hy, fun h => h ▸ rfl⟩

theorem InjOn.congr (h₁ : InjOn f₁ s) (h : EqOn f₁ f₂ s) : InjOn f₂ s := fun x hx y hy => h hx ▸ h hy ▸ h₁ hx hy

theorem EqOn.inj_on_iff (H : EqOn f₁ f₂ s) : InjOn f₁ s ↔ InjOn f₂ s :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem InjOn.mono (h : s₁ ⊆ s₂) (ht : InjOn f s₂) : InjOn f s₁ := fun x hx y hy H => ht (h hx) (h hy) H

theorem inj_on_union (h : Disjoint s₁ s₂) :
    InjOn f (s₁ ∪ s₂) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ ∀, ∀ x ∈ s₁, ∀, ∀ y ∈ s₂, ∀, f x ≠ f y := by
  refine' ⟨fun H => ⟨H.mono <| subset_union_left _ _, H.mono <| subset_union_right _ _, _⟩, _⟩
  · intro x hx y hy hxy
    obtain rfl : x = y
    exact H (Or.inl hx) (Or.inr hy) hxy
    exact h ⟨hx, hy⟩
    
  · rintro ⟨h₁, h₂, h₁₂⟩
    rintro x (hx | hx) y (hy | hy) hxy
    exacts[h₁ hx hy hxy, (h₁₂ _ hx _ hy hxy).elim, (h₁₂ _ hy _ hx hxy.symm).elim, h₂ hx hy hxy]
    

theorem inj_on_insert {f : α → β} {s : Set α} {a : α} (has : a ∉ s) :
    Set.InjOn f (insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s := by
  have : Disjoint s {a} := fun x ⟨hxs, (hxa : x = a)⟩ => has (hxa ▸ hxs)
  rw [← union_singleton, inj_on_union this]
  simp

theorem injective_iff_inj_on_univ : Injective f ↔ InjOn f Univ :=
  ⟨fun h x hx y hy hxy => h hxy, fun h _ _ heq => h trivialₓ trivialₓ HEq⟩

theorem inj_on_of_injective (h : Injective f) (s : Set α) : InjOn f s := fun x hx y hy hxy => h hxy

alias inj_on_of_injective ← Function.Injective.inj_on

theorem InjOn.comp (hg : InjOn g t) (hf : InjOn f s) (h : MapsTo f s t) : InjOn (g ∘ f) s := fun x hx y hy heq =>
  hf hx hy <| hg (h hx) (h hy) HEq

theorem inj_on_iff_injective : InjOn f s ↔ Injective (s.restrict f) :=
  ⟨fun H a b h => Subtype.eq <| H a.2 b.2 h, fun H a as b bs h => congr_argₓ Subtype.val <| @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

alias inj_on_iff_injective ↔ Set.InjOn.injective _

theorem inj_on_preimage {B : Set (Set β)} (hB : B ⊆ 𝒫 Range f) : InjOn (Preimage f) B := fun s hs t ht hst =>
  (preimage_eq_preimage' (hB hs) (hB ht)).1 hst

theorem InjOn.mem_of_mem_image {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (h : x ∈ s) (h₁ : f x ∈ f '' s₁) : x ∈ s₁ :=
  let ⟨x', h', Eq⟩ := h₁
  hf (hs h') h Eq ▸ h'

theorem InjOn.mem_image_iff {x} (hf : InjOn f s) (hs : s₁ ⊆ s) (hx : x ∈ s) : f x ∈ f '' s₁ ↔ x ∈ s₁ :=
  ⟨hf.mem_of_mem_image hs hx, mem_image_of_mem f⟩

theorem InjOn.preimage_image_inter (hf : InjOn f s) (hs : s₁ ⊆ s) : f ⁻¹' (f '' s₁) ∩ s = s₁ :=
  ext fun x => ⟨fun ⟨h₁, h₂⟩ => hf.mem_of_mem_image hs h₂ h₁, fun h => ⟨mem_image_of_mem _ h, hs h⟩⟩

theorem EqOn.cancel_left (h : s.EqOn (g ∘ f₁) (g ∘ f₂)) (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn f₁ f₂ := fun a ha => hg (hf₁ ha) (hf₂ ha) (h ha)

theorem InjOn.cancel_left (hg : t.InjOn g) (hf₁ : s.MapsTo f₁ t) (hf₂ : s.MapsTo f₂ t) :
    s.EqOn (g ∘ f₁) (g ∘ f₂) ↔ s.EqOn f₁ f₂ :=
  ⟨fun h => h.cancel_left hg hf₁ hf₂, EqOn.comp_left⟩

/-! ### Surjectivity on a set -/


/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  t ⊆ f '' s

theorem SurjOn.subset_range (h : SurjOn f s t) : t ⊆ Range f :=
  Subset.trans h <| image_subset_range f s

theorem surj_on_iff_exists_map_subtype :
    SurjOn f s t ↔ ∃ (t' : Set β)(g : s → t'), t ⊆ t' ∧ Surjective g ∧ ∀ x : s, f x = g x :=
  ⟨fun h => ⟨_, (maps_to_image f s).restrict f s _, h, surjective_maps_to_image_restrict _ _, fun _ => rfl⟩, fun y hy =>
    let ⟨x, hx⟩ := hg ⟨y, htt' hy⟩
    ⟨x, x.2, by
      rw [hfg, hx, Subtype.coe_mk]⟩⟩

theorem surj_on_empty (f : α → β) (s : Set α) : SurjOn f s ∅ :=
  empty_subset _

theorem surj_on_image (f : α → β) (s : Set α) : SurjOn f s (f '' s) :=
  subset.rfl

theorem SurjOn.comap_nonempty (h : SurjOn f s t) (ht : t.Nonempty) : s.Nonempty :=
  (ht.mono h).of_image

theorem SurjOn.congr (h : SurjOn f₁ s t) (H : EqOn f₁ f₂ s) : SurjOn f₂ s t := by
  rwa [surj_on, ← H.image_eq]

theorem EqOn.surj_on_iff (h : EqOn f₁ f₂ s) : SurjOn f₁ s t ↔ SurjOn f₂ s t :=
  ⟨fun H => H.congr h, fun H => H.congr h.symm⟩

theorem SurjOn.mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (hf : SurjOn f s₁ t₂) : SurjOn f s₂ t₁ :=
  Subset.trans ht <| Subset.trans hf <| image_subset _ hs

theorem SurjOn.union (h₁ : SurjOn f s t₁) (h₂ : SurjOn f s t₂) : SurjOn f s (t₁ ∪ t₂) := fun x hx =>
  hx.elim (fun hx => h₁ hx) fun hx => h₂ hx

theorem SurjOn.union_union (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) : SurjOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  (h₁.mono (subset_union_left _ _) (Subset.refl _)).union (h₂.mono (subset_union_right _ _) (Subset.refl _))

theorem SurjOn.inter_inter (h₁ : SurjOn f s₁ t₁) (h₂ : SurjOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) :
    SurjOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := by
  intro y hy
  rcases h₁ hy.1 with ⟨x₁, hx₁, rfl⟩
  rcases h₂ hy.2 with ⟨x₂, hx₂, heq⟩
  obtain rfl : x₁ = x₂ := h (Or.inl hx₁) (Or.inr hx₂) HEq.symm
  exact mem_image_of_mem f ⟨hx₁, hx₂⟩

theorem SurjOn.inter (h₁ : SurjOn f s₁ t) (h₂ : SurjOn f s₂ t) (h : InjOn f (s₁ ∪ s₂)) : SurjOn f (s₁ ∩ s₂) t :=
  inter_self t ▸ h₁.inter_inter h₂ h

theorem SurjOn.comp (hg : SurjOn g t p) (hf : SurjOn f s t) : SurjOn (g ∘ f) s p :=
  Subset.trans hg <| Subset.trans (image_subset g hf) <| image_comp g f s ▸ Subset.refl _

theorem surjective_iff_surj_on_univ : Surjective f ↔ SurjOn f Univ Univ := by
  simp [surjective, surj_on, subset_def]

theorem surj_on_iff_surjective : SurjOn f s Univ ↔ Surjective (s.restrict f) :=
  ⟨fun H b =>
    let ⟨a, as, e⟩ := @H b trivialₓ
    ⟨⟨a, as⟩, e⟩,
    fun H b _ =>
    let ⟨⟨a, as⟩, e⟩ := H b
    ⟨a, as, e⟩⟩

theorem SurjOn.image_eq_of_maps_to (h₁ : SurjOn f s t) (h₂ : MapsTo f s t) : f '' s = t :=
  eq_of_subset_of_subset h₂.image_subset h₁

theorem image_eq_iff_surj_on_maps_to : f '' s = t ↔ s.SurjOn f t ∧ s.MapsTo f t := by
  refine' ⟨_, fun h => h.1.image_eq_of_maps_to h.2⟩
  rintro rfl
  exact ⟨s.surj_on_image f, s.maps_to_image f⟩

theorem SurjOn.maps_to_compl (h : SurjOn f s t) (h' : Injective f) : MapsTo f (sᶜ) (tᶜ) := fun x hs ht =>
  let ⟨x', hx', HEq⟩ := h ht
  hs <| h' HEq ▸ hx'

theorem MapsTo.surj_on_compl (h : MapsTo f s t) (h' : Surjective f) : SurjOn f (sᶜ) (tᶜ) :=
  h'.forall.2 fun x ht => (mem_image_of_mem _) fun hs => ht (h hs)

theorem EqOn.cancel_right (hf : s.EqOn (g₁ ∘ f) (g₂ ∘ f)) (hf' : s.SurjOn f t) : t.EqOn g₁ g₂ := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hf' hb
  exact hf ha

theorem SurjOn.cancel_right (hf : s.SurjOn f t) (hf' : s.MapsTo f t) : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ t.EqOn g₁ g₂ :=
  ⟨fun h => h.cancel_right hf, fun h => h.compRight hf'⟩

theorem eq_on_comp_right_iff : s.EqOn (g₁ ∘ f) (g₂ ∘ f) ↔ (f '' s).EqOn g₁ g₂ :=
  (s.surj_on_image f).cancel_right <| s.maps_to_image f

/-! ### Bijectivity -/


/-- `f` is bijective from `s` to `t` if `f` is injective on `s` and `f '' s = t`. -/
def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop :=
  MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t

theorem BijOn.maps_to (h : BijOn f s t) : MapsTo f s t :=
  h.left

theorem BijOn.inj_on (h : BijOn f s t) : InjOn f s :=
  h.right.left

theorem BijOn.surj_on (h : BijOn f s t) : SurjOn f s t :=
  h.right.right

theorem BijOn.mk (h₁ : MapsTo f s t) (h₂ : InjOn f s) (h₃ : SurjOn f s t) : BijOn f s t :=
  ⟨h₁, h₂, h₃⟩

theorem bij_on_empty (f : α → β) : BijOn f ∅ ∅ :=
  ⟨maps_to_empty f ∅, inj_on_empty f, surj_on_empty f ∅⟩

theorem BijOn.inter (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) : BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  ⟨h₁.MapsTo.inter_inter h₂.MapsTo, h₁.InjOn.mono <| inter_subset_left _ _, h₁.SurjOn.inter_inter h₂.SurjOn h⟩

theorem BijOn.union (h₁ : BijOn f s₁ t₁) (h₂ : BijOn f s₂ t₂) (h : InjOn f (s₁ ∪ s₂)) : BijOn f (s₁ ∪ s₂) (t₁ ∪ t₂) :=
  ⟨h₁.MapsTo.union_union h₂.MapsTo, h, h₁.SurjOn.union_union h₂.SurjOn⟩

theorem BijOn.subset_range (h : BijOn f s t) : t ⊆ Range f :=
  h.SurjOn.subset_range

theorem InjOn.bij_on_image (h : InjOn f s) : BijOn f s (f '' s) :=
  BijOn.mk (maps_to_image f s) h (Subset.refl _)

theorem BijOn.congr (h₁ : BijOn f₁ s t) (h : EqOn f₁ f₂ s) : BijOn f₂ s t :=
  BijOn.mk (h₁.MapsTo.congr h) (h₁.InjOn.congr h) (h₁.SurjOn.congr h)

theorem EqOn.bij_on_iff (H : EqOn f₁ f₂ s) : BijOn f₁ s t ↔ BijOn f₂ s t :=
  ⟨fun h => h.congr H, fun h => h.congr H.symm⟩

theorem BijOn.image_eq (h : BijOn f s t) : f '' s = t :=
  h.SurjOn.image_eq_of_maps_to h.MapsTo

theorem BijOn.comp (hg : BijOn g t p) (hf : BijOn f s t) : BijOn (g ∘ f) s p :=
  BijOn.mk (hg.MapsTo.comp hf.MapsTo) (hg.InjOn.comp hf.InjOn hf.MapsTo) (hg.SurjOn.comp hf.SurjOn)

theorem BijOn.bijective (h : BijOn f s t) : Bijective ((t.codRestrict (s.restrict f)) fun x => h.MapsTo x.val_prop) :=
  ⟨fun x y h' => Subtype.ext <| h.InjOn x.2 y.2 <| Subtype.ext_iff.1 h', fun ⟨y, hy⟩ =>
    let ⟨x, hx, hxy⟩ := h.SurjOn hy
    ⟨⟨x, hx⟩, Subtype.eq hxy⟩⟩

theorem bijective_iff_bij_on_univ : Bijective f ↔ BijOn f Univ Univ :=
  Iff.intro
    (fun h =>
      let ⟨inj, surj⟩ := h
      ⟨maps_to_univ f _, inj.InjOn _, Iff.mp surjective_iff_surj_on_univ surj⟩)
    fun h =>
    let ⟨map, inj, surj⟩ := h
    ⟨Iff.mpr injective_iff_inj_on_univ inj, Iff.mpr surjective_iff_surj_on_univ surj⟩

theorem BijOn.compl (hst : BijOn f s t) (hf : Bijective f) : BijOn f (sᶜ) (tᶜ) :=
  ⟨hst.SurjOn.maps_to_compl hf.1, hf.1.InjOn _, hst.MapsTo.surj_on_compl hf.2⟩

/-! ### left inverse -/


/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
def LeftInvOn (f' : β → α) (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ s → f' (f x) = x

theorem LeftInvOn.eq_on (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s :=
  h

theorem LeftInvOn.eq (h : LeftInvOn f' f s) {x} (hx : x ∈ s) : f' (f x) = x :=
  h hx

theorem LeftInvOn.congr_left (h₁ : LeftInvOn f₁' f s) {t : Set β} (h₁' : MapsTo f s t) (heq : EqOn f₁' f₂' t) :
    LeftInvOn f₂' f s := fun x hx => HEq (h₁' hx) ▸ h₁ hx

theorem LeftInvOn.congr_right (h₁ : LeftInvOn f₁' f₁ s) (heq : EqOn f₁ f₂ s) : LeftInvOn f₁' f₂ s := fun x hx =>
  HEq hx ▸ h₁ hx

theorem LeftInvOn.inj_on (h : LeftInvOn f₁' f s) : InjOn f s := fun x₁ h₁ x₂ h₂ heq =>
  calc
    x₁ = f₁' (f x₁) := Eq.symm <| h h₁
    _ = f₁' (f x₂) := congr_argₓ f₁' HEq
    _ = x₂ := h h₂
    

theorem LeftInvOn.surj_on (h : LeftInvOn f' f s) (hf : MapsTo f s t) : SurjOn f' t s := fun x hx => ⟨f x, hf hx, h hx⟩

theorem LeftInvOn.maps_to (h : LeftInvOn f' f s) (hf : SurjOn f s t) : MapsTo f' t s := fun y hy => by
  let ⟨x, hs, hx⟩ := hf hy
  rwa [← hx, h hs]

theorem LeftInvOn.comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
    LeftInvOn (f' ∘ g') (g ∘ f) s := fun x h =>
  calc
    (f' ∘ g') ((g ∘ f) x) = f' (f x) := congr_argₓ f' (hg' (hf h))
    _ = x := hf' h
    

theorem LeftInvOn.mono (hf : LeftInvOn f' f s) (ht : s₁ ⊆ s) : LeftInvOn f' f s₁ := fun x hx => hf (ht hx)

theorem LeftInvOn.image_inter' (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' s₁ ∩ f '' s := by
  apply subset.antisymm
  · rintro _ ⟨x, ⟨h₁, h⟩, rfl⟩
    exact
      ⟨by
        rwa [mem_preimage, hf h], mem_image_of_mem _ h⟩
    
  · rintro _ ⟨h₁, ⟨x, h, rfl⟩⟩
    exact
      mem_image_of_mem _
        ⟨by
          rwa [← hf h], h⟩
    

theorem LeftInvOn.image_inter (hf : LeftInvOn f' f s) : f '' (s₁ ∩ s) = f' ⁻¹' (s₁ ∩ s) ∩ f '' s := by
  rw [hf.image_inter']
  refine' subset.antisymm _ (inter_subset_inter_left _ (preimage_mono <| inter_subset_left _ _))
  rintro _ ⟨h₁, x, hx, rfl⟩
  exact
    ⟨⟨h₁, by
        rwa [hf hx]⟩,
      mem_image_of_mem _ hx⟩

theorem LeftInvOn.image_image (hf : LeftInvOn f' f s) : f' '' (f '' s) = s := by
  rw [image_image, image_congr hf, image_id']

theorem LeftInvOn.image_image' (hf : LeftInvOn f' f s) (hs : s₁ ⊆ s) : f' '' (f '' s₁) = s₁ :=
  (hf.mono hs).image_image

/-! ### Right inverse -/


/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
@[reducible]
def RightInvOn (f' : β → α) (f : α → β) (t : Set β) : Prop :=
  LeftInvOn f f' t

theorem RightInvOn.eq_on (h : RightInvOn f' f t) : EqOn (f ∘ f') id t :=
  h

theorem RightInvOn.eq (h : RightInvOn f' f t) {y} (hy : y ∈ t) : f (f' y) = y :=
  h hy

theorem LeftInvOn.right_inv_on_image (h : LeftInvOn f' f s) : RightInvOn f' f (f '' s) := fun y ⟨x, hx, Eq⟩ =>
  Eq ▸ congr_argₓ f <| h.Eq hx

theorem RightInvOn.congr_left (h₁ : RightInvOn f₁' f t) (heq : EqOn f₁' f₂' t) : RightInvOn f₂' f t :=
  h₁.congr_right HEq

theorem RightInvOn.congr_right (h₁ : RightInvOn f' f₁ t) (hg : MapsTo f' t s) (heq : EqOn f₁ f₂ s) :
    RightInvOn f' f₂ t :=
  LeftInvOn.congr_left h₁ hg HEq

theorem RightInvOn.surj_on (hf : RightInvOn f' f t) (hf' : MapsTo f' t s) : SurjOn f s t :=
  hf.SurjOn hf'

theorem RightInvOn.maps_to (h : RightInvOn f' f t) (hf : SurjOn f' t s) : MapsTo f s t :=
  h.MapsTo hf

theorem RightInvOn.comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
    RightInvOn (f' ∘ g') (g ∘ f) p :=
  hg.comp hf g'pt

theorem RightInvOn.mono (hf : RightInvOn f' f t) (ht : t₁ ⊆ t) : RightInvOn f' f t₁ :=
  hf.mono ht

theorem InjOn.right_inv_on_of_left_inv_on (hf : InjOn f s) (hf' : LeftInvOn f f' t) (h₁ : MapsTo f s t)
    (h₂ : MapsTo f' t s) : RightInvOn f f' s := fun x h => hf (h₂ <| h₁ h) h (hf' (h₁ h))

theorem eq_on_of_left_inv_on_of_right_inv_on (h₁ : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t) (h : MapsTo f₂' t s) :
    EqOn f₁' f₂' t := fun y hy =>
  calc
    f₁' y = (f₁' ∘ f ∘ f₂') y := congr_argₓ f₁' (h₂ hy).symm
    _ = f₂' y := h₁ (h hy)
    

theorem SurjOn.left_inv_on_of_right_inv_on (hf : SurjOn f s t) (hf' : RightInvOn f f' s) : LeftInvOn f f' t :=
  fun y hy => by
  let ⟨x, hx, HEq⟩ := hf hy
  rw [← HEq, hf' hx]

/-! ### Two-side inverses -/


/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t

theorem InvOn.symm (h : InvOn f' f s t) : InvOn f f' t s :=
  ⟨h.right, h.left⟩

theorem InvOn.mono (h : InvOn f' f s t) (hs : s₁ ⊆ s) (ht : t₁ ⊆ t) : InvOn f' f s₁ t₁ :=
  ⟨h.1.mono hs, h.2.mono ht⟩

/-- If functions `f'` and `f` are inverse on `s` and `t`, `f` maps `s` into `t`, and `f'` maps `t`
into `s`, then `f` is a bijection between `s` and `t`. The `maps_to` arguments can be deduced from
`surj_on` statements using `left_inv_on.maps_to` and `right_inv_on.maps_to`. -/
theorem InvOn.bij_on (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : MapsTo f' t s) : BijOn f s t :=
  ⟨hf, h.left.InjOn, h.right.SurjOn hf'⟩

end Set

/-! ### `inv_fun_on` is a left/right inverse -/


namespace Function

variable [Nonempty α] {s : Set α} {f : α → β} {a : α} {b : β}

attribute [local instance] Classical.propDecidable

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. For a computable version, see `function.injective.inv_of_mem_range`. -/
noncomputable def invFunOn (f : α → β) (s : Set α) (b : β) : α :=
  if h : ∃ a, a ∈ s ∧ f a = b then Classical.some h else Classical.choice ‹Nonempty α›

theorem inv_fun_on_posₓ (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s ∧ f (invFunOn f s b) = b := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_pos h] <;> exact Classical.some_spec h

theorem inv_fun_on_memₓ (h : ∃ a ∈ s, f a = b) : invFunOn f s b ∈ s :=
  (inv_fun_on_posₓ h).left

theorem inv_fun_on_eqₓ (h : ∃ a ∈ s, f a = b) : f (invFunOn f s b) = b :=
  (inv_fun_on_posₓ h).right

theorem inv_fun_on_negₓ (h : ¬∃ a ∈ s, f a = b) : invFunOn f s b = Classical.choice ‹Nonempty α› := by
  rw [bex_def] at h <;> rw [inv_fun_on, dif_neg h]

end Function

namespace Set

open Function

variable {s s₁ s₂ : Set α} {t : Set β} {f : α → β}

theorem InjOn.left_inv_on_inv_fun_on [Nonempty α] (h : InjOn f s) : LeftInvOn (invFunOn f s) f s := fun a ha =>
  have : ∃ a' ∈ s, f a' = f a := ⟨a, ha, rfl⟩
  h (inv_fun_on_memₓ this) ha (inv_fun_on_eqₓ this)

theorem InjOn.inv_fun_on_image [Nonempty α] (h : InjOn f s₂) (ht : s₁ ⊆ s₂) : invFunOn f s₂ '' (f '' s₁) = s₁ :=
  h.left_inv_on_inv_fun_on.image_image' ht

theorem SurjOn.right_inv_on_inv_fun_on [Nonempty α] (h : SurjOn f s t) : RightInvOn (invFunOn f s) f t := fun y hy =>
  inv_fun_on_eq <| mem_image_iff_bex.1 <| h hy

theorem BijOn.inv_on_inv_fun_on [Nonempty α] (h : BijOn f s t) : InvOn (invFunOn f s) f s t :=
  ⟨h.InjOn.left_inv_on_inv_fun_on, h.SurjOn.right_inv_on_inv_fun_on⟩

theorem SurjOn.inv_on_inv_fun_on [Nonempty α] (h : SurjOn f s t) : InvOn (invFunOn f s) f (invFunOn f s '' t) t := by
  refine' ⟨_, h.right_inv_on_inv_fun_on⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [h.right_inv_on_inv_fun_on hy]

theorem SurjOn.maps_to_inv_fun_on [Nonempty α] (h : SurjOn f s t) : MapsTo (invFunOn f s) t s := fun y hy =>
  mem_preimage.2 <| inv_fun_on_mem <| mem_image_iff_bex.1 <| h hy

theorem SurjOn.bij_on_subset [Nonempty α] (h : SurjOn f s t) : BijOn f (invFunOn f s '' t) t := by
  refine' h.inv_on_inv_fun_on.bij_on _ (maps_to_image _ _)
  rintro _ ⟨y, hy, rfl⟩
  rwa [h.right_inv_on_inv_fun_on hy]

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (s' «expr ⊆ » s)
theorem surj_on_iff_exists_bij_on_subset : SurjOn f s t ↔ ∃ (s' : _)(_ : s' ⊆ s), BijOn f s' t := by
  constructor
  · rcases eq_empty_or_nonempty t with (rfl | ht)
    · exact fun _ => ⟨∅, empty_subset _, bij_on_empty f⟩
      
    · intro h
      have : Nonempty α := ⟨Classical.some (h.comap_nonempty ht)⟩
      exact ⟨_, h.maps_to_inv_fun_on.image_subset, h.bij_on_subset⟩
      
    
  · rintro ⟨s', hs', hfs'⟩
    exact hfs'.surj_on.mono hs' (subset.refl _)
    

theorem preimage_inv_fun_of_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∈ s) : invFun f ⁻¹' s = f '' s ∪ Range fᶜ := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · simp [left_inverse_inv_fun hf _, hf.mem_set_image]
    
  · simp [mem_preimage, inv_fun_neg hx, h, hx]
    

theorem preimage_inv_fun_of_not_mem [n : Nonempty α] {f : α → β} (hf : Injective f) {s : Set α}
    (h : Classical.choice n ∉ s) : invFun f ⁻¹' s = f '' s := by
  ext x
  rcases em (x ∈ range f) with (⟨a, rfl⟩ | hx)
  · rw [mem_preimage, left_inverse_inv_fun hf, hf.mem_set_image]
    
  · have : x ∉ f '' s := fun h' => hx (image_subset_range _ _ h')
    simp only [mem_preimage, inv_fun_neg hx, h, this]
    

end Set

/-! ### Monotone -/


namespace Monotone

variable [Preorderₓ α] [Preorderₓ β] {f : α → β}

protected theorem restrict (h : Monotone f) (s : Set α) : Monotone (s.restrict f) := fun x y hxy => h hxy

protected theorem cod_restrict (h : Monotone f) {s : Set β} (hs : ∀ x, f x ∈ s) : Monotone (s.codRestrict f hs) :=
  h

protected theorem range_factorization (h : Monotone f) : Monotone (Set.rangeFactorization f) :=
  h

end Monotone

/-! ### Piecewise defined function -/


namespace Set

variable {δ : α → Sort y} (s : Set α) (f g : ∀ i, δ i)

@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Set α))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]

@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (Set.Univ : Set α))] : piecewise Set.Univ f g = f := by
  ext i
  simp [piecewise]

@[simp]
theorem piecewise_insert_self {j : α} [∀ i, Decidable (i ∈ insert j s)] : (insert j s).piecewise f g j = f j := by
  simp [piecewise]

variable [∀ j, Decidable (j ∈ s)]

instance Compl.decidableMem (j : α) : Decidable (j ∈ sᶜ) :=
  Not.decidable

theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j) := by
  simp [piecewise]
  ext i
  by_cases' h : i = j
  · rw [h]
    simp
    
  · by_cases' h' : i ∈ s <;> simp [h, h']
    

@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
  if_pos hi

@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
  if_neg hi

theorem piecewise_singleton (x : α) [∀ y, Decidable (y ∈ ({x} : Set α))] [DecidableEq α] (f g : α → β) :
    piecewise {x} f g = Function.update g x (f x) := by
  ext y
  by_cases' hy : y = x
  · subst y
    simp
    
  · simp [hy]
    

theorem piecewise_eq_on (f g : α → β) : EqOn (s.piecewise f g) f s := fun _ => piecewise_eq_of_mem _ _ _

theorem piecewise_eq_on_compl (f g : α → β) : EqOn (s.piecewise f g) g (sᶜ) := fun _ => piecewise_eq_of_not_mem _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (i «expr ∉ » s)
theorem piecewise_le {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g : ∀ i, δ i}
    (h₁ : ∀, ∀ i ∈ s, ∀, f₁ i ≤ g i) (h₂ : ∀ i _ : i ∉ s, f₂ i ≤ g i) : s.piecewise f₁ f₂ ≤ g := fun i =>
  if h : i ∈ s then by
    simp [*]
  else by
    simp [*]

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (i «expr ∉ » s)
theorem le_piecewise {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g : ∀ i, δ i}
    (h₁ : ∀, ∀ i ∈ s, ∀, g i ≤ f₁ i) (h₂ : ∀ i _ : i ∉ s, g i ≤ f₂ i) : g ≤ s.piecewise f₁ f₂ :=
  @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (i «expr ∉ » s)
theorem piecewise_le_piecewise {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g₁ g₂ : ∀ i, δ i} (h₁ : ∀, ∀ i ∈ s, ∀, f₁ i ≤ g₁ i) (h₂ : ∀ i _ : i ∉ s, f₂ i ≤ g₂ i) :
    s.piecewise f₁ f₂ ≤ s.piecewise g₁ g₂ := by
  apply piecewise_le <;> intros <;> simp [*]

@[simp]
theorem piecewise_insert_of_ne {i j : α} (h : i ≠ j) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g i = s.piecewise f g i := by
  simp [piecewise, h]

@[simp]
theorem piecewise_compl [∀ i, Decidable (i ∈ sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
  funext fun x =>
    if hx : x ∈ s then by
      simp [hx]
    else by
      simp [hx]

@[simp]
theorem piecewise_range_comp {ι : Sort _} (f : ι → α) [∀ j, Decidable (j ∈ Range f)] (g₁ g₂ : α → β) :
    (Range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
  comp_eq_of_eq_on_range <| piecewise_eq_on _ _ _

theorem MapsTo.piecewise_ite {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α → β} [∀ i, Decidable (i ∈ s)]
    (h₁ : MapsTo f₁ (s₁ ∩ s) (t₁ ∩ t)) (h₂ : MapsTo f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ)) :
    MapsTo (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) := by
  refine' (h₁.congr _).union_union (h₂.congr _)
  exacts[(piecewise_eq_on s f₁ f₂).symm.mono (inter_subset_right _ _),
    (piecewise_eq_on_compl s f₁ f₂).symm.mono (inter_subset_right _ _)]

theorem eq_on_piecewise {f f' g : α → β} {t} : EqOn (s.piecewise f f') g t ↔ EqOn f g (t ∩ s) ∧ EqOn f' g (t ∩ sᶜ) := by
  simp only [eq_on, ← forall_and_distrib]
  refine' forall_congrₓ fun a => _
  by_cases' a ∈ s <;> simp [*]

theorem EqOn.piecewise_ite' {f f' g : α → β} {t t'} (h : EqOn f g (t ∩ s)) (h' : EqOn f' g (t' ∩ sᶜ)) :
    EqOn (s.piecewise f f') g (s.ite t t') := by
  simp [eq_on_piecewise, *]

theorem EqOn.piecewise_ite {f f' g : α → β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t') :
    EqOn (s.piecewise f f') g (s.ite t t') :=
  (h.mono (inter_subset_left _ _)).piecewise_ite' s (h'.mono (inter_subset_left _ _))

theorem piecewise_preimage (f g : α → β) t : s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
  ext fun x => by
    by_cases' x ∈ s <;> simp [*, Set.Ite]

theorem apply_piecewise {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) {x : α} :
    h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x := by
  by_cases' hx : x ∈ s <;> simp [hx]

theorem apply_piecewise₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) {x : α} :
    h x (s.piecewise f g x) (s.piecewise f' g' x) =
      s.piecewise (fun x => h x (f x) (f' x)) (fun x => h x (g x) (g' x)) x :=
  by
  by_cases' hx : x ∈ s <;> simp [hx]

theorem piecewise_op {δ' : α → Sort _} (h : ∀ i, δ i → δ' i) :
    (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x) :=
  funext fun x => (apply_piecewise _ _ _ _).symm

theorem piecewise_op₂ {δ' δ'' : α → Sort _} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) :
    (s.piecewise (fun x => h x (f x) (f' x)) fun x => h x (g x) (g' x)) = fun x =>
      h x (s.piecewise f g x) (s.piecewise f' g' x) :=
  funext fun x => (apply_piecewise₂ _ _ _ _ _ _).symm

@[simp]
theorem piecewise_same : s.piecewise f f = f := by
  ext x
  by_cases' hx : x ∈ s <;> simp [hx]

theorem range_piecewise (f g : α → β) : Range (s.piecewise f g) = f '' s ∪ g '' sᶜ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    by_cases' h : x ∈ s <;> [left, right] <;> use x <;> simp [h]
    
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all
    

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (y «expr ∉ » s)
theorem injective_piecewise_iff {f g : α → β} :
    Injective (s.piecewise f g) ↔ InjOn f s ∧ InjOn g (sᶜ) ∧ ∀, ∀ x ∈ s, ∀ y _ : y ∉ s, f x ≠ g y := by
  rw [injective_iff_inj_on_univ, ← union_compl_self s, inj_on_union (@disjoint_compl_right _ s _),
    (piecewise_eq_on s f g).inj_on_iff, (piecewise_eq_on_compl s f g).inj_on_iff]
  refine' and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congrₓ fun x hx y hy => _)
  rw [piecewise_eq_of_mem s f g hx, piecewise_eq_of_not_mem s f g hy]

theorem piecewise_mem_pi {δ : α → Type _} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ Pi t t')
    (hg : g ∈ Pi t t') : s.piecewise f g ∈ Pi t t' := by
  intro i ht
  by_cases' hs : i ∈ s <;> simp [hf i ht, hg i ht, hs]

@[simp]
theorem pi_piecewise {ι : Type _} {α : ι → Type _} (s s' : Set ι) (t t' : ∀ i, Set (α i)) [∀ x, Decidable (x ∈ s')] :
    Pi s (s'.piecewise t t') = Pi (s ∩ s') t ∩ Pi (s \ s') t' := by
  ext x
  simp only [mem_pi, mem_inter_eq, ← forall_and_distrib]
  refine' forall_congrₓ fun i => _
  by_cases' hi : i ∈ s' <;> simp [*]

theorem univ_pi_piecewise {ι : Type _} {α : ι → Type _} (s : Set ι) (t : ∀ i, Set (α i)) [∀ x, Decidable (x ∈ s)] :
    Pi Univ (s.piecewise t fun _ => Univ) = Pi s t := by
  simp

end Set

theorem StrictMonoOn.inj_on [LinearOrderₓ α] [Preorderₓ β] {f : α → β} {s : Set α} (H : StrictMonoOn f s) : s.InjOn f :=
  fun x hx y hy hxy => show Ordering.eq.Compares x y from (H.Compares hx hy).1 hxy

theorem StrictAntiOn.inj_on [LinearOrderₓ α] [Preorderₓ β] {f : α → β} {s : Set α} (H : StrictAntiOn f s) : s.InjOn f :=
  @StrictMonoOn.inj_on α βᵒᵈ _ _ f s H

theorem StrictMonoOn.comp [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α} {t : Set β}
    (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) : StrictMonoOn (g ∘ f) s :=
  fun x hx y hy hxy => hg (hs hx) (hs hy) <| hf hx hy hxy

theorem StrictMonoOn.comp_strict_anti_on [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictMonoOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s :=
  fun x hx y hy hxy => hg (hs hy) (hs hx) <| hf hx hy hxy

theorem StrictAntiOn.comp [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α} {t : Set β}
    (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) : StrictMonoOn (g ∘ f) s :=
  fun x hx y hy hxy => hg (hs hy) (hs hx) <| hf hx hy hxy

theorem StrictAntiOn.comp_strict_mono_on [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : StrictAntiOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s :=
  fun x hx y hy hxy => hg (hs hx) (hs hy) <| hf hx hy hxy

theorem StrictMono.cod_restrict [Preorderₓ α] [Preorderₓ β] {f : α → β} (hf : StrictMono f) {s : Set β}
    (hs : ∀ x, f x ∈ s) : StrictMono (Set.codRestrict f s hs) :=
  hf

namespace Function

open Set

variable {fa : α → α} {fb : β → β} {f : α → β} {g : β → γ} {s t : Set α}

theorem Injective.comp_inj_on (hg : Injective g) (hf : s.InjOn f) : s.InjOn (g ∘ f) :=
  (hg.InjOn Univ).comp hf (maps_to_univ _ _)

theorem Surjective.surj_on (hf : Surjective f) (s : Set β) : SurjOn f Univ s :=
  (surjective_iff_surj_on_univ.1 hf).mono (Subset.refl _) (subset_univ _)

theorem LeftInverse.left_inv_on {g : β → α} (h : LeftInverse f g) (s : Set β) : LeftInvOn f g s := fun x hx => h x

theorem RightInverse.right_inv_on {g : β → α} (h : RightInverse f g) (s : Set α) : RightInvOn f g s := fun x hx => h x

theorem LeftInverse.right_inv_on_range {g : β → α} (h : LeftInverse f g) : RightInvOn f g (Range g) :=
  forall_range_iff.2 fun i => congr_argₓ g (h i)

namespace Semiconj

theorem maps_to_image (h : Semiconj f fa fb) (ha : MapsTo fa s t) : MapsTo fb (f '' s) (f '' t) := fun y ⟨x, hx, hy⟩ =>
  hy ▸ ⟨fa x, ha hx, h x⟩

theorem maps_to_range (h : Semiconj f fa fb) : MapsTo fb (Range f) (Range f) := fun y ⟨x, hy⟩ => hy ▸ ⟨fa x, h x⟩

theorem surj_on_image (h : Semiconj f fa fb) (ha : SurjOn fa s t) : SurjOn fb (f '' s) (f '' t) := by
  rintro y ⟨x, hxt, rfl⟩
  rcases ha hxt with ⟨x, hxs, rfl⟩
  rw [h x]
  exact mem_image_of_mem _ (mem_image_of_mem _ hxs)

theorem surj_on_range (h : Semiconj f fa fb) (ha : Surjective fa) : SurjOn fb (Range f) (Range f) := by
  rw [← image_univ]
  exact h.surj_on_image (ha.surj_on univ)

theorem inj_on_image (h : Semiconj f fa fb) (ha : InjOn fa s) (hf : InjOn f (fa '' s)) : InjOn fb (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ H
  simp only [← h.eq] at H
  exact congr_argₓ f (ha hx hy <| hf (mem_image_of_mem fa hx) (mem_image_of_mem fa hy) H)

theorem inj_on_range (h : Semiconj f fa fb) (ha : Injective fa) (hf : InjOn f (Range fa)) : InjOn fb (Range f) := by
  rw [← image_univ] at *
  exact h.inj_on_image (ha.inj_on univ) hf

theorem bij_on_image (h : Semiconj f fa fb) (ha : BijOn fa s t) (hf : InjOn f t) : BijOn fb (f '' s) (f '' t) :=
  ⟨h.maps_to_image ha.MapsTo, h.inj_on_image ha.InjOn (ha.image_eq.symm ▸ hf), h.surj_on_image ha.SurjOn⟩

theorem bij_on_range (h : Semiconj f fa fb) (ha : Bijective fa) (hf : Injective f) : BijOn fb (Range f) (Range f) := by
  rw [← image_univ]
  exact h.bij_on_image (bijective_iff_bij_on_univ.1 ha) (hf.inj_on univ)

theorem maps_to_preimage (h : Semiconj f fa fb) {s t : Set β} (hb : MapsTo fb s t) : MapsTo fa (f ⁻¹' s) (f ⁻¹' t) :=
  fun x hx => by
  simp only [mem_preimage, h x, hb hx]

theorem inj_on_preimage (h : Semiconj f fa fb) {s : Set β} (hb : InjOn fb s) (hf : InjOn f (f ⁻¹' s)) :
    InjOn fa (f ⁻¹' s) := by
  intro x hx y hy H
  have := congr_argₓ f H
  rw [h.eq, h.eq] at this
  exact hf hx hy (hb hx hy this)

end Semiconj

theorem update_comp_eq_of_not_mem_range' {α β : Sort _} {γ : β → Sort _} [DecidableEq β] (g : ∀ b, γ b) {f : α → β}
    {i : β} (a : γ i) (h : i ∉ Set.Range f) : (fun j => (Function.update g i a) (f j)) = fun j => g (f j) :=
  (update_comp_eq_of_forall_ne' _ _) fun x hx => h ⟨x, hx⟩

/-- Non-dependent version of `function.update_comp_eq_of_not_mem_range'` -/
theorem update_comp_eq_of_not_mem_range {α β γ : Sort _} [DecidableEq β] (g : β → γ) {f : α → β} {i : β} (a : γ)
    (h : i ∉ Set.Range f) : Function.update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_not_mem_range' g a h

theorem insert_inj_on (s : Set α) : sᶜ.InjOn fun a => insert a s := fun a ha b _ => (insert_inj ha).1

end Function

