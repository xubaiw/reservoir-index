/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Order.Closure
import Mathbin.ModelTheory.Semantics
import Mathbin.ModelTheory.Encoding

/-!
# First-Order Substructures
This file defines substructures of first-order structures in a similar manner to the various
substructures appearing in the algebra library.

## Main Definitions
* A `first_order.language.substructure` is defined so that `L.substructure M` is the type of all
substructures of the `L`-structure `M`.
* `first_order.language.substructure.closure` is defined so that if `s : set M`, `closure L s` is
the least substructure of `M` containing `s`.
* `first_order.language.substructure.comap` is defined so that `s.comap f` is the preimage of the
substructure `s` under the homomorphism `f`, as a substructure.
* `first_order.language.substructure.map` is defined so that `s.map f` is the image of the
substructure `s` under the homomorphism `f`, as a substructure.
* `first_order.language.hom.range` is defined so that `f.map` is the range of the
the homomorphism `f`, as a substructure.
* `first_order.language.hom.dom_restrict` and `first_order.language.hom.cod_restrict` restrict
the domain and codomain respectively of first-order homomorphisms to substructures.
* `first_order.language.embedding.dom_restrict` and `first_order.language.embedding.cod_restrict`
restrict the domain and codomain respectively of first-order embeddings to substructures.
* `first_order.language.substructure.inclusion` is the inclusion embedding between substructures.

## Main Results
* `L.substructure M` forms a `complete_lattice`.

-/


universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N P : Type _}

variable [L.Structure M] [L.Structure N] [L.Structure P]

open FirstOrder Cardinal

open Structure Cardinal

section ClosedUnder

open Set

variable {n : ℕ} (f : L.Functions n) (s : Set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
def ClosedUnder : Prop :=
  ∀ x : Finₓ n → M, (∀ i : Finₓ n, x i ∈ s) → funMap f x ∈ s

variable (L)

@[simp]
theorem closed_under_univ : ClosedUnder f (Univ : Set M) := fun _ _ => mem_univ _

variable {L f s} {t : Set M}

namespace ClosedUnder

theorem inter (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ∩ t) := fun x h =>
  mem_inter (hs x fun i => mem_of_mem_inter_left (h i)) (ht x fun i => mem_of_mem_inter_right (h i))

theorem inf (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s⊓t) :=
  hs.inter ht

variable {S : Set (Set M)}

theorem Inf (hS : ∀ s, s ∈ S → ClosedUnder f s) : ClosedUnder f (inf S) := fun x h s hs => hS s hs x fun i => h i s hs

end ClosedUnder

end ClosedUnder

variable (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
structure Substructure where
  Carrier : Set M
  fun_mem : ∀ {n}, ∀ f : L.Functions n, ClosedUnder f carrier

variable {L} {M}

namespace Substructure

instance : SetLike (L.Substructure M) M :=
  ⟨Substructure.Carrier, fun p q h => by
    cases p <;> cases q <;> congr⟩

/-- See Note [custom simps projection] -/
def Simps.Coe (S : L.Substructure M) : Set M :=
  S

initialize_simps_projections Substructure (Carrier → coe)

@[simp]
theorem mem_carrier {s : L.Substructure M} {x : M} : x ∈ s.Carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {S T : L.Substructure M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
protected def copy (S : L.Substructure M) (s : Set M) (hs : s = S) : L.Substructure M where
  Carrier := s
  fun_mem := fun n f => hs.symm ▸ S.fun_mem f

end Substructure

variable {S : L.Substructure M}

theorem Term.realize_mem {α : Type _} (t : L.Term α) (xs : α → M) (h : ∀ a, xs a ∈ S) : t.realize xs ∈ S := by
  induction' t with a n f ts ih
  · exact h a
    
  · exact substructure.fun_mem _ _ _ ih
    

namespace Substructure

@[simp]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem constants_mem (c : L.Constants) : ↑c ∈ S :=
  mem_carrier.2 (S.fun_mem c _ Finₓ.elim0)

/-- The substructure `M` of the structure `M`. -/
instance : HasTop (L.Substructure M) :=
  ⟨{ Carrier := Set.Univ, fun_mem := fun n f x h => Set.mem_univ _ }⟩

instance : Inhabited (L.Substructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.Substructure M) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.Substructure M) : Set M) = Set.Univ :=
  rfl

/-- The inf of two substructures is their intersection. -/
instance : HasInf (L.Substructure M) :=
  ⟨fun S₁ S₂ => { Carrier := S₁ ∩ S₂, fun_mem := fun n f => (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
theorem coe_inf (p p' : L.Substructure M) : ((p⊓p' : L.Substructure M) : Set M) = p ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : L.Substructure M} {x : M} : x ∈ p⊓p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : HasInfₓ (L.Substructure M) :=
  ⟨fun s =>
    { Carrier := ⋂ t ∈ s, ↑t,
      fun_mem := fun n f =>
        ClosedUnder.Inf
          (by
            rintro _ ⟨t, rfl⟩
            by_cases' h : t ∈ s
            · simpa [h] using t.fun_mem f
              
            · simp [h]
              ) }⟩

@[simp, norm_cast]
theorem coe_Inf (S : Set (L.Substructure M)) : ((inf S : L.Substructure M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_Inf {S : Set (L.Substructure M)} {x : M} : x ∈ inf S ↔ ∀, ∀ p ∈ S, ∀, x ∈ p :=
  Set.mem_Inter₂

theorem mem_infi {ι : Sort _} {S : ι → L.Substructure M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [infi, mem_Inf, Set.forall_range_iff]

@[simp, norm_cast]
theorem coe_infi {ι : Sort _} {S : ι → L.Substructure M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [infi, coe_Inf, Set.bInter_range]

/-- Substructures of a structure form a complete lattice. -/
instance : CompleteLattice (L.Substructure M) :=
  { (completeLatticeOfInf (L.Substructure M)) fun s =>
      IsGlb.of_image (fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe) is_glb_binfi with
    le := (· ≤ ·), lt := (· < ·), top := ⊤, le_top := fun S x hx => mem_top x, inf := (·⊓·), inf := HasInfₓ.inf,
    le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩, inf_le_left := fun a b x => And.left,
    inf_le_right := fun a b x => And.right }

variable (L)

/-- The `L.substructure` generated by a set. -/
def closure : LowerAdjoint (coe : L.Substructure M → Set M) :=
  ⟨fun s => inf { S | s ⊆ S }, fun s S => ⟨Set.Subset.trans fun x hx => mem_Inf.2 fun S hS => hS hx, fun h => Inf_le h⟩⟩

variable {L} {s : Set M}

theorem mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.Substructure M, s ⊆ S → x ∈ S :=
  mem_Inf

/-- The substructure generated by a set includes the set. -/
@[simp]
theorem subset_closure : s ⊆ closure L s :=
  (closure L).le_closure s

theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure L s) : P ∉ s := fun h => hP (subset_closure h)

@[simp]
theorem closed (S : L.Substructure M) : (closure L).Closed (S : Set M) :=
  congr rfl ((closure L).eq_of_le Set.Subset.rfl fun x xS => mem_closure.2 fun T hT => hT xS)

open Set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
theorem closure_le : closure L s ≤ S ↔ s ⊆ S :=
  (closure L).closure_le_closed_iff_le s S.Closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
  (closure L).Monotone h

theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
  (closure L).eq_of_le h₁ h₂

theorem coe_closure_eq_range_term_realize : (closure L s : Set M) = Range (@Term.realizeₓ L _ _ _ (coe : s → M)) := by
  let S : L.substructure M := ⟨range (term.realize coe), fun n f x hx => _⟩
  · change _ = (S : Set M)
    rw [← SetLike.ext'_iff]
    refine' closure_eq_of_le (fun x hx => ⟨var ⟨x, hx⟩, rfl⟩) (le_Inf fun S' hS' => _)
    · rintro _ ⟨t, rfl⟩
      exact t.realize_mem _ fun i => hS' i.2
      
    
  · simp only [mem_range] at *
    refine' ⟨func f fun i => Classical.some (hx i), _⟩
    simp only [term.realize, fun i => Classical.some_spec (hx i)]
    

instance small_closure [Small.{u} s] : Small.{u} (closure L s) := by
  rw [← SetLike.coe_sort_coe, substructure.coe_closure_eq_range_term_realize]
  exact small_range _

theorem mem_closure_iff_exists_term {x : M} : x ∈ closure L s ↔ ∃ t : L.Term s, t.realize (coe : s → M) = x := by
  rw [← SetLike.mem_coe, coe_closure_eq_range_term_realize, mem_range]

theorem lift_card_closure_le_card_term : Cardinal.lift.{max u w} (# (closure L s)) ≤ # (L.Term s) := by
  rw [← SetLike.coe_sort_coe, coe_closure_eq_range_term_realize]
  rw [← Cardinal.lift_id'.{w, max u w} (# (L.term s))]
  exact Cardinal.mk_range_le_lift

theorem lift_card_closure_le :
    Cardinal.lift.{max u w, w} (# (closure L s)) ≤
      max ω (Cardinal.lift.{max u w, w} (# s) + Cardinal.lift.{max u w, u} (# (Σi, L.Functions i))) :=
  by
  refine' lift_card_closure_le_card_term.trans (term.card_le.trans _)
  rw [mk_sum, lift_umax', lift_umax]

variable (L)

theorem _root_.set.countable.substructure_closure [L.CountableFunctions] (h : s.Countable) :
    Nonempty (Encodable (closure L s)) := by
  have : Nonempty (Encodable s) := h
  rw [encodable_iff, ← lift_le_omega]
  exact lift_card_closure_le_card_term.trans term.card_le_omega

variable {L} (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure L s) (Hs : ∀, ∀ x ∈ s, ∀, p x)
    (Hfun : ∀ {n : ℕ} f : L.Functions n, ClosedUnder f (SetOf p)) : p x :=
  (@closure_le L M _ ⟨SetOf p, fun n => Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_eliminator]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure L s = ⊤) (Hs : ∀, ∀ x ∈ s, ∀, p x)
    (Hfun : ∀ {n : ℕ} f : L.Functions n, ClosedUnder f (SetOf p)) : p x := by
  have : ∀, ∀ x ∈ closure L s, ∀, p x := fun x hx => closure_induction hx Hs fun n => Hfun
  simpa [hs] using this x

variable (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure L M _) coe where
  choice := fun s _ => closure L s
  gc := (closure L).gc
  le_l_u := fun s => subset_closure
  choice_eq := fun s h => rfl

variable {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp]
theorem closure_eq : closure L (S : Set M) = S :=
  (Substructure.gi L M).l_u_eq S

@[simp]
theorem closure_empty : closure L (∅ : Set M) = ⊥ :=
  (Substructure.gi L M).gc.l_bot

@[simp]
theorem closure_univ : closure L (Univ : Set M) = ⊤ :=
  @coe_top L M _ ▸ closure_eq ⊤

theorem closure_union (s t : Set M) : closure L (s ∪ t) = closure L s⊔closure L t :=
  (Substructure.gi L M).gc.l_sup

theorem closure_Union {ι} (s : ι → Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
  (Substructure.gi L M).gc.l_supr

instance small_bot : Small.{u} (⊥ : L.Substructure M) := by
  rw [← closure_empty]
  exact substructure.small_closure

/-!
### `comap` and `map`
-/


/-- The preimage of a substructure along a homomorphism is a substructure. -/
@[simps]
def comap (φ : M →[L] N) (S : L.Substructure N) : L.Substructure M where
  Carrier := φ ⁻¹' S
  fun_mem := fun n f x hx => by
    rw [mem_preimage, φ.map_fun]
    exact S.fun_mem f (φ ∘ x) hx

@[simp]
theorem mem_comap {S : L.Substructure N} {f : M →[L] N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

theorem comap_comap (S : L.Substructure P) (g : N →[L] P) (f : M →[L] N) : (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem comap_id (S : L.Substructure P) : S.comap (Hom.id _ _) = S :=
  ext
    (by
      simp )

/-- The image of a substructure along a homomorphism is a substructure. -/
@[simps]
def map (φ : M →[L] N) (S : L.Substructure M) : L.Substructure N where
  Carrier := φ '' S
  fun_mem := fun n f x hx =>
    (mem_image _ _ _).1
      ⟨funMap f fun i => Classical.some (hx i), S.fun_mem f _ fun i => (Classical.some_spec (hx i)).1, by
        simp only [hom.map_fun, SetLike.mem_coe]
        exact congr rfl (funext fun i => (Classical.some_spec (hx i)).2)⟩

@[simp]
theorem mem_map {f : M →[L] N} {S : L.Substructure M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex

theorem mem_map_of_mem (f : M →[L] N) {S : L.Substructure M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

theorem apply_coe_mem_map (f : M →[L] N) (S : L.Substructure M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.Prop

theorem map_map (g : N →[L] P) (f : M →[L] N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image _ _ _

theorem map_le_iff_le_comap {f : M →[L] N} {S : L.Substructure M} {T : L.Substructure N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

theorem gc_map_comap (f : M →[L] N) : GaloisConnection (map f) (comap f) := fun S T => map_le_iff_le_comap

theorem map_le_of_le_comap {T : L.Substructure N} {f : M →[L] N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

theorem le_comap_of_map_le {T : L.Substructure N} {f : M →[L] N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

theorem le_comap_map {f : M →[L] N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

theorem map_comap_le {S : L.Substructure N} {f : M →[L] N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

theorem monotone_map {f : M →[L] N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

theorem monotone_comap {f : M →[L] N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp]
theorem map_comap_map {f : M →[L] N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp]
theorem comap_map_comap {S : L.Substructure N} {f : M →[L] N} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

theorem map_sup (S T : L.Substructure M) (f : M →[L] N) : (S⊔T).map f = S.map f⊔T.map f :=
  (gc_map_comap f).l_sup

theorem map_supr {ι : Sort _} (f : M →[L] N) (s : ι → L.Substructure M) : (supr s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supr

theorem comap_inf (S T : L.Substructure N) (f : M →[L] N) : (S⊓T).comap f = S.comap f⊓T.comap f :=
  (gc_map_comap f).u_inf

theorem comap_infi {ι : Sort _} (f : M →[L] N) (s : ι → L.Substructure N) : (infi s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infi

@[simp]
theorem map_bot (f : M →[L] N) : (⊥ : L.Substructure M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : M →[L] N) : (⊤ : L.Substructure N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
theorem map_id (S : L.Substructure M) : S.map (Hom.id L M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

theorem map_closure (f : M →[L] N) (s : Set M) : (closure L s).map f = closure L (f '' s) :=
  Eq.symm <|
    closure_eq_of_le (Set.image_subset f subset_closure) <|
      map_le_iff_le_comap.2 <| closure_le.2 fun x hx => subset_closure ⟨x, hx, rfl⟩

@[simp]
theorem closure_image (f : M →[L] N) : closure L (f '' s) = map f (closure L s) :=
  (map_closure f s).symm

section GaloisCoinsertion

variable {ι : Type _} {f : M →[L] N} (hf : Function.Injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp [mem_comap, mem_map, hf.eq_iff]

theorem comap_map_eq_of_injective (S : L.Substructure M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

theorem comap_inf_map_of_injective (S T : L.Substructure M) : (S.map f⊓T.map f).comap f = S⊓T :=
  (gciMapComap hf).u_inf_l _ _

theorem comap_infi_map_of_injective (S : ι → L.Substructure M) : (⨅ i, (S i).map f).comap f = infi S :=
  (gciMapComap hf).u_infi_l _

theorem comap_sup_map_of_injective (S T : L.Substructure M) : (S.map f⊔T.map f).comap f = S⊔T :=
  (gciMapComap hf).u_sup_l _ _

theorem comap_supr_map_of_injective (S : ι → L.Substructure M) : (⨆ i, (S i).map f).comap f = supr S :=
  (gciMapComap hf).u_supr_l _

theorem map_le_map_iff_of_injective {S T : L.Substructure M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gciMapComap hf).l_le_l_iff

theorem map_strict_mono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strict_mono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : M →[L] N} (hf : Function.Surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2
      ⟨y, by
        simp [hy, h]⟩

theorem map_comap_eq_of_surjective (S : L.Substructure N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

theorem map_inf_comap_of_surjective (S T : L.Substructure N) : (S.comap f⊓T.comap f).map f = S⊓T :=
  (giMapComap hf).l_inf_u _ _

theorem map_infi_comap_of_surjective (S : ι → L.Substructure N) : (⨅ i, (S i).comap f).map f = infi S :=
  (giMapComap hf).l_infi_u _

theorem map_sup_comap_of_surjective (S T : L.Substructure N) : (S.comap f⊔T.comap f).map f = S⊔T :=
  (giMapComap hf).l_sup_u _ _

theorem map_supr_comap_of_surjective (S : ι → L.Substructure N) : (⨆ i, (S i).comap f).map f = supr S :=
  (giMapComap hf).l_supr_u _

theorem comap_le_comap_iff_of_surjective {S T : L.Substructure N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (giMapComap hf).u_le_u_iff

theorem comap_strict_mono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strict_mono_u

end GaloisInsertion

instance inducedStructure {S : L.Substructure M} : L.Structure S where
  funMap := fun n f x => ⟨funMap f fun i => x i, S.fun_mem f (fun i => x i) fun i => (x i).2⟩
  rel_map := fun n r x => RelMap r fun i => (x i : M)

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def subtype (S : L.Substructure M) : S ↪[L] M where
  toFun := coe
  inj' := Subtype.coe_injective

@[simp]
theorem coe_subtype : ⇑S.Subtype = coe :=
  rfl

/-- The equivalence between the maximal substructure of a structure and the structure itself. -/
def topEquiv : (⊤ : L.Substructure M) ≃[L] M where
  toFun := subtype ⊤
  invFun := fun m => ⟨m, mem_top m⟩
  left_inv := fun m => by
    simp
  right_inv := fun m => rfl

@[simp]
theorem coe_top_equiv : ⇑(topEquiv : (⊤ : L.Substructure M) ≃[L] M) = coe :=
  rfl

/-- A dependent version of `substructure.closure_induction`. -/
@[elab_as_eliminator]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure L s → Prop} (Hs : ∀ x h : x ∈ s, p x (subset_closure h))
    (Hfun : ∀ {n : ℕ} f : L.Functions n, ClosedUnder f { x | ∃ hx, p x hx }) {x} (hx : x ∈ closure L s) : p x hx := by
  refine' Exists.elim _ fun hc : p x hx => hc
  exact closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) @Hfun

end Substructure

namespace Lhom

open Substructure

variable {L' : Language} [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]

include φ

/-- Reduces the language of a substructure along a language hom. -/
def substructureReduct : L'.Substructure M ↪o L.Substructure M where
  toFun := fun S =>
    { Carrier := S,
      fun_mem := fun n f x hx => by
        have h := S.fun_mem (φ.on_function f) x hx
        simp only [is_expansion_on.map_on_function, substructure.mem_carrier] at h
        exact h }
  inj' := fun S T h => by
    simp only [SetLike.coe_set_eq] at h
    exact h
  map_rel_iff' := fun S T => Iff.rfl

@[simp]
theorem mem_substructure_reduct {x : M} {S : L'.Substructure M} : x ∈ φ.substructureReduct S ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_substructure_reduct {S : L'.Substructure M} : (φ.substructureReduct S : Set M) = ↑S :=
  rfl

end Lhom

namespace Substructure

/-- Turns any substructure containing a constant set `A` into a `L[[A]]`-substructure. -/
def withConstants (S : L.Substructure M) {A : Set M} (h : A ⊆ S) : L[[A]].Substructure M where
  Carrier := S
  fun_mem := fun n f => by
    cases f
    · exact S.fun_mem f
      
    · cases n
      · exact fun _ _ => h f.2
        
      · exact Pempty.elimₓ f
        
      

variable {A : Set M} {s : Set M} (h : A ⊆ S)

@[simp]
theorem mem_with_constants {x : M} : x ∈ S.withConstants h ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_with_constants : (S.withConstants h : Set M) = ↑S :=
  rfl

@[simp]
theorem reduct_with_constants : (L.lhomWithConstants A).substructureReduct (S.withConstants h) = S := by
  ext
  simp

theorem subset_closure_with_constants : A ⊆ closure (L[[A]]) s := by
  intro a ha
  simp only [SetLike.mem_coe]
  let a' : L[[A]].Constants := Sum.inr ⟨a, ha⟩
  exact constants_mem a'

theorem closure_with_constants_eq :
    closure (L[[A]]) s = (closure L (A ∪ s)).withConstants ((A.subset_union_left s).trans subset_closure) := by
  refine' closure_eq_of_le ((A.subset_union_right s).trans subset_closure) _
  rw [← (L.Lhom_with_constants A).substructureReduct.le_iff_le]
  simp only [subset_closure, reduct_with_constants, closure_le, Lhom.coe_substructure_reduct, Set.union_subset_iff,
    and_trueₓ]
  · exact subset_closure_with_constants
    
  · infer_instance
    
  · infer_instance
    

end Substructure

namespace Hom

open Substructure

/-- The restriction of a first-order hom to a substructure `s ⊆ M` gives a hom `s → N`. -/
@[simps]
def domRestrict (f : M →[L] N) (p : L.Substructure M) : p →[L] N :=
  f.comp p.Subtype.toHom

/-- A first-order hom `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted to a
hom `M → p`. -/
@[simps]
def codRestrict (p : L.Substructure N) (f : M →[L] N) (h : ∀ c, f c ∈ p) : M →[L] p where
  toFun := fun c => ⟨f c, h c⟩
  map_rel' := fun n R x h => f.map_rel R x h

@[simp]
theorem comp_cod_restrict (f : M →[L] N) (g : N →[L] P) (p : L.Substructure P) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →[L] p) = codRestrict p (g.comp f) fun b => h _ :=
  ext fun b => rfl

@[simp]
theorem subtype_comp_cod_restrict (f : M →[L] N) (p : L.Substructure N) (h : ∀ b, f b ∈ p) :
    p.Subtype.toHom.comp (codRestrict p f h) = f :=
  ext fun b => rfl

/-- The range of a first-order hom `f : M → N` is a submodule of `N`.
See Note [range copy pattern]. -/
def range (f : M →[L] N) : L.Substructure N :=
  (map f ⊤).copy (Set.Range f) Set.image_univ.symm

theorem range_coe (f : M →[L] N) : (range f : Set N) = Set.Range f :=
  rfl

@[simp]
theorem mem_range {f : M →[L] N} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl

theorem range_eq_map (f : M →[L] N) : f.range = map f ⊤ := by
  ext
  simp

theorem mem_range_self (f : M →[L] N) (x : M) : f x ∈ f.range :=
  ⟨x, rfl⟩

@[simp]
theorem range_id : range (id L M) = ⊤ :=
  SetLike.coe_injective Set.range_id

theorem range_comp (f : M →[L] N) (g : N →[L] P) : range (g.comp f : M →[L] P) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range (f : M →[L] N) (g : N →[L] P) : range (g.comp f : M →[L] P) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

theorem range_eq_top {f : M →[L] N} : range f = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff, range_coe, coe_top, Set.range_iff_surjective]

theorem range_le_iff_comap {f : M →[L] N} {p : L.Substructure N} : range f ≤ p ↔ comap f p = ⊤ := by
  rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

theorem map_le_range {f : M →[L] N} {p : L.Substructure M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

/-- The substructure of elements `x : M` such that `f x = g x` -/
def eqLocus (f g : M →[L] N) : Substructure L M where
  Carrier := { x : M | f x = g x }
  fun_mem := fun n fn x hx => by
    have h : f ∘ x = g ∘ x := by
      ext
      repeat'
        rw [Function.comp_applyₓ]
      apply hx
    simp [h]

/-- If two `L.hom`s are equal on a set, then they are equal on its substructure closure. -/
theorem eq_on_closure {f g : M →[L] N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure L s) :=
  show closure L s ≤ f.eqLocus g from closure_le.2 h

theorem eq_of_eq_on_top {f g : M →[L] N} (h : Set.EqOn f g (⊤ : Substructure L M)) : f = g :=
  ext fun x => h trivialₓ

variable {s : Set M}

theorem eq_of_eq_on_dense (hs : closure L s = ⊤) {f g : M →[L] N} (h : s.EqOn f g) : f = g :=
  eq_of_eq_on_top <| hs ▸ eq_on_closure h

end Hom

namespace Embedding

open Substructure

/-- The restriction of a first-order embedding to a substructure `s ⊆ M` gives an embedding `s → N`.
-/
def domRestrict (f : M ↪[L] N) (p : L.Substructure M) : p ↪[L] N :=
  f.comp p.Subtype

@[simp]
theorem dom_restrict_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) : f.domRestrict p x = f x :=
  rfl

/-- A first-order embedding `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted
to an embedding `M → p`. -/
def codRestrict (p : L.Substructure N) (f : M ↪[L] N) (h : ∀ c, f c ∈ p) : M ↪[L] p where
  toFun := f.toHom.codRestrict p h
  inj' := fun a b ab => f.Injective (Subtype.mk_eq_mk.1 ab)
  map_fun' := fun n F x => (f.toHom.codRestrict p h).map_fun' F x
  map_rel' := fun n r x => by
    simp only
    rw [← p.subtype.map_rel, Function.comp.assoc]
    change rel_map r (hom.comp p.subtype.to_hom (f.to_hom.cod_restrict p h) ∘ x) ↔ _
    rw [hom.subtype_comp_cod_restrict, ← f.map_rel]
    rfl

@[simp]
theorem cod_restrict_apply (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) : (codRestrict p f h x : N) = f x :=
  rfl

@[simp]
theorem comp_cod_restrict (f : M ↪[L] N) (g : N ↪[L] P) (p : L.Substructure P) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M ↪[L] p) = codRestrict p (g.comp f) fun b => h _ :=
  ext fun b => rfl

@[simp]
theorem subtype_comp_cod_restrict (f : M ↪[L] N) (p : L.Substructure N) (h : ∀ b, f b ∈ p) :
    p.Subtype.comp (codRestrict p f h) = f :=
  ext fun b => rfl

/-- The equivalence between a substructure `s` and its image `s.map f.to_hom`, where `f` is an
  embedding. -/
noncomputable def substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) : s ≃[L] s.map f.toHom where
  toFun := codRestrict (s.map f.toHom) (f.domRestrict s) fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩
  invFun := fun n => ⟨Classical.some n.2, (Classical.some_spec n.2).1⟩
  left_inv := fun ⟨m, hm⟩ =>
    Subtype.mk_eq_mk.2
      (f.Injective
        (Classical.some_spec (codRestrict (s.map f.toHom) (f.domRestrict s) (fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩) ⟨m, hm⟩).2).2)
  right_inv := fun ⟨n, hn⟩ => Subtype.mk_eq_mk.2 (Classical.some_spec hn).2

@[simp]
theorem substructure_equiv_map_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) :
    (f.substructureEquivMap p x : N) = f x :=
  rfl

/-- The equivalence between the domain and the range of an embedding `f`. -/
noncomputable def equivRange (f : M ↪[L] N) : M ≃[L] f.toHom.range where
  toFun := codRestrict f.toHom.range f f.toHom.mem_range_self
  invFun := fun n => Classical.some n.2
  left_inv := fun m => f.Injective (Classical.some_spec (codRestrict f.toHom.range f f.toHom.mem_range_self m).2)
  right_inv := fun ⟨n, hn⟩ => Subtype.mk_eq_mk.2 (Classical.some_spec hn)

@[simp]
theorem equiv_range_apply (f : M ↪[L] N) (x : M) : (f.equivRange x : N) = f x :=
  rfl

end Embedding

namespace Equivₓ

theorem to_hom_range (f : M ≃[L] N) : f.toHom.range = ⊤ := by
  ext n
  simp only [hom.mem_range, coe_to_hom, substructure.mem_top, iff_trueₓ]
  exact ⟨f.symm n, apply_symm_apply _ _⟩

end Equivₓ

namespace Substructure

/-- The embedding associated to an inclusion of substructures. -/
def inclusion {S T : L.Substructure M} (h : S ≤ T) : S ↪[L] T :=
  S.Subtype.codRestrict _ fun x => h x.2

@[simp]
theorem coe_inclusion {S T : L.Substructure M} (h : S ≤ T) : (inclusion h : S → T) = Set.inclusion h :=
  rfl

theorem range_subtype (S : L.Substructure M) : S.Subtype.toHom.range = S := by
  ext x
  simp only [hom.mem_range, embedding.coe_to_hom, coeSubtype]
  refine' ⟨_, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rintro ⟨⟨y, hy⟩, rfl⟩
  exact hy

end Substructure

end Language

end FirstOrder

