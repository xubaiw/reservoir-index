/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathbin.ModelTheory.Basic

/-!
# Language Maps
Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions
* A `first_order.language.Lhom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
* A `first_order.language.Lequiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
* `first_order.language.with_constants` is defined so that if `M` is an `L.Structure` and
  `A : set M`, `L.with_constants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

open Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure Lhom where
  onFunction : ∀ {n}, L.Functions n → L'.Functions n
  onRelation : ∀ {n}, L.Relations n → L'.Relations n

-- mathport name: «expr →ᴸ »
infixl:10 " →ᴸ " => Lhom

-- \^L
variable {L L'}

namespace Lhom

/-- Defines a map between languages defined with `language.mk₂`. -/
protected def mk₂ {c f₁ f₂ : Type u} {r₁ r₂ : Type v} (φ₀ : c → L'.Constants) (φ₁ : f₁ → L'.Functions 1)
    (φ₂ : f₂ → L'.Functions 2) (φ₁' : r₁ → L'.Relations 1) (φ₂' : r₂ → L'.Relations 2) :
    Language.mk₂ c f₁ f₂ r₁ r₂ →ᴸ L' :=
  ⟨fun n => Nat.casesOn n φ₀ fun n => Nat.casesOn n φ₁ fun n => Nat.casesOn n φ₂ fun _ => Pempty.elimₓ, fun n =>
    Nat.casesOn n Pempty.elimₓ fun n => Nat.casesOn n φ₁' fun n => Nat.casesOn n φ₂' fun _ => Pempty.elimₓ⟩

variable (ϕ : L →ᴸ L')

/-- Pulls a structure back along a language map. -/
def reduct (M : Type _) [L'.Structure M] : L.Structure M where
  funMap := fun n f xs => funMap (ϕ.onFunction f) xs
  rel_map := fun n r xs => RelMap (ϕ.onRelation r) xs

/-- The identity language homomorphism. -/
@[simps]
protected def id (L : Language) : L →ᴸ L :=
  ⟨fun n => id, fun n => id⟩

instance : Inhabited (L →ᴸ L) :=
  ⟨Lhom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps]
protected def sumInl : L →ᴸ L.Sum L' :=
  ⟨fun n => Sum.inl, fun n => Sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps]
protected def sumInr : L' →ᴸ L.Sum L' :=
  ⟨fun n => Sum.inr, fun n => Sum.inr⟩

variable (L L')

/-- The inclusion of an empty language into any other language. -/
@[simps]
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L →ᴸ L' :=
  ⟨fun n => (IsRelational.empty_functions n).elim, fun n => (IsAlgebraic.empty_relations n).elim⟩

variable {L L'} {L'' : Language}

@[ext]
protected theorem funext {F G : L →ᴸ L'} (h_fun : F.onFunction = G.onFunction) (h_rel : F.onRelation = G.onRelation) :
    F = G := by
  cases' F with Ff Fr
  cases' G with Gf Gr
  simp only [*]
  exact And.intro h_fun h_rel

instance [L.IsAlgebraic] [L.IsRelational] : Unique (L →ᴸ L') :=
  ⟨⟨Lhom.ofIsEmpty L L'⟩, fun _ => Lhom.funext (Subsingleton.elimₓ _ _) (Subsingleton.elimₓ _ _)⟩

theorem mk₂_funext {c f₁ f₂ : Type u} {r₁ r₂ : Type v} {F G : Language.mk₂ c f₁ f₂ r₁ r₂ →ᴸ L'}
    (h0 : ∀ c : (Language.mk₂ c f₁ f₂ r₁ r₂).Constants, F.onFunction c = G.onFunction c)
    (h1 : ∀ f : (Language.mk₂ c f₁ f₂ r₁ r₂).Functions 1, F.onFunction f = G.onFunction f)
    (h2 : ∀ f : (Language.mk₂ c f₁ f₂ r₁ r₂).Functions 2, F.onFunction f = G.onFunction f)
    (h1' : ∀ r : (Language.mk₂ c f₁ f₂ r₁ r₂).Relations 1, F.onRelation r = G.onRelation r)
    (h2' : ∀ r : (Language.mk₂ c f₁ f₂ r₁ r₂).Relations 2, F.onRelation r = G.onRelation r) : F = G :=
  Lhom.funext
    (funext fun n =>
      Nat.casesOn n (funext h0) fun n =>
        Nat.casesOn n (funext h1) fun n => Nat.casesOn n (funext h2) fun n => funext fun f => Pempty.elimₓ f)
    (funext fun n =>
      Nat.casesOn n (funext fun r => Pempty.elimₓ r) fun n =>
        Nat.casesOn n (funext h1') fun n => Nat.casesOn n (funext h2') fun n => funext fun r => Pempty.elimₓ r)

/-- The composition of two language homomorphisms. -/
@[simps]
def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
  ⟨fun n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩

-- mathport name: «expr ∘ »
local infixl:60 " ∘ " => Lhom.comp

@[simp]
theorem id_comp (F : L →ᴸ L') : Lhom.id L' ∘ F = F := by
  cases F
  rfl

@[simp]
theorem comp_id (F : L →ᴸ L') : F ∘ Lhom.id L = F := by
  cases F
  rfl

theorem comp_assoc {L3 : Language} (F : L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') : F ∘ G ∘ H = F ∘ (G ∘ H) :=
  rfl

section SumElim

variable (ψ : L'' →ᴸ L')

/-- A language map defined on two factors of a sum. -/
@[simps]
protected def sumElim : L.Sum L'' →ᴸ L' where
  onFunction := fun n => Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation := fun n => Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

theorem sum_elim_comp_inl (ψ : L'' →ᴸ L') : ϕ.sum_elim ψ ∘ Lhom.sum_inl = ϕ :=
  Lhom.funext (funext fun _ => rfl) (funext fun _ => rfl)

theorem sum_elim_comp_inr (ψ : L'' →ᴸ L') : ϕ.sum_elim ψ ∘ Lhom.sum_inr = ψ :=
  Lhom.funext (funext fun _ => rfl) (funext fun _ => rfl)

theorem sum_elim_inl_inr : Lhom.sumInl.sum_elim Lhom.sumInr = Lhom.id (L.Sum L') :=
  Lhom.funext (funext fun _ => Sum.elim_inl_inr) (funext fun _ => Sum.elim_inl_inr)

theorem comp_sum_elim {L3 : Language} (θ : L' →ᴸ L3) : θ ∘ ϕ.sum_elim ψ = (θ ∘ ϕ).sum_elim (θ ∘ ψ) :=
  Lhom.funext (funext fun n => Sum.comp_elim _ _ _) (funext fun n => Sum.comp_elim _ _ _)

end SumElim

section SumMap

variable {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
def sumMap : L.Sum L₁ →ᴸ L'.Sum L₂ where
  onFunction := fun n => Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation := fun n => Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

@[simp]
theorem sum_map_comp_inl : ϕ.sum_map ψ ∘ Lhom.sum_inl = Lhom.sum_inl ∘ ϕ :=
  Lhom.funext (funext fun _ => rfl) (funext fun _ => rfl)

@[simp]
theorem sum_map_comp_inr : ϕ.sum_map ψ ∘ Lhom.sum_inr = Lhom.sum_inr ∘ ψ :=
  Lhom.funext (funext fun _ => rfl) (funext fun _ => rfl)

end SumMap

/-- A language homomorphism is injective when all the maps between symbol types are. -/
protected structure Injective : Prop where
  onFunction {n} : Function.Injective (onFunction ϕ : L.Functions n → L'.Functions n)
  onRelation {n} : Function.Injective (onRelation ϕ : L.Relations n → L'.Relations n)

/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
class IsExpansionOn (M : Type _) [L.Structure M] [L'.Structure M] : Prop where
  map_on_function : ∀ {n} (f : L.Functions n) (x : Finₓ n → M), funMap (ϕ.onFunction f) x = funMap f x
  map_on_relation : ∀ {n} (R : L.Relations n) (x : Finₓ n → M), RelMap (ϕ.onRelation R) x = RelMap R x

@[simp]
theorem map_on_function {M : Type _} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (f : L.Functions n)
    (x : Finₓ n → M) : funMap (ϕ.onFunction f) x = funMap f x :=
  IsExpansionOn.map_on_function f x

@[simp]
theorem map_on_relation {M : Type _} [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M] {n} (R : L.Relations n)
    (x : Finₓ n → M) : RelMap (ϕ.onRelation R) x = RelMap R x :=
  IsExpansionOn.map_on_relation R x

instance id_is_expansion_on (M : Type _) [L.Structure M] : IsExpansionOn (Lhom.id L) M :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

instance of_is_empty_is_expansion_on (M : Type _) [L.Structure M] [L'.Structure M] [L.IsAlgebraic] [L.IsRelational] :
    IsExpansionOn (Lhom.ofIsEmpty L L') M :=
  ⟨fun n => (IsRelational.empty_functions n).elim, fun n => (IsAlgebraic.empty_relations n).elim⟩

instance sum_elim_is_expansion_on {L'' : Language} (ψ : L'' →ᴸ L') (M : Type _) [L.Structure M] [L'.Structure M]
    [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] : (ϕ.sum_elim ψ).IsExpansionOn M :=
  ⟨fun _ f _ =>
    Sum.casesOn f
      (by
        simp )
      (by
        simp ),
    fun _ R _ =>
    Sum.casesOn R
      (by
        simp )
      (by
        simp )⟩

instance sum_map_is_expansion_on {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂) (M : Type _) [L.Structure M] [L'.Structure M]
    [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] : (ϕ.sum_map ψ).IsExpansionOn M :=
  ⟨fun _ f _ =>
    Sum.casesOn f
      (by
        simp )
      (by
        simp ),
    fun _ R _ =>
    Sum.casesOn R
      (by
        simp )
      (by
        simp )⟩

instance sum_inl_is_expansion_on (M : Type _) [L.Structure M] [L'.Structure M] :
    (Lhom.sumInl : L →ᴸ L.Sum L').IsExpansionOn M :=
  ⟨fun _ f _ => rfl, fun _ R _ => rfl⟩

instance sum_inr_is_expansion_on (M : Type _) [L.Structure M] [L'.Structure M] :
    (Lhom.sumInr : L' →ᴸ L.Sum L').IsExpansionOn M :=
  ⟨fun _ f _ => rfl, fun _ R _ => rfl⟩

@[simp]
theorem fun_map_sum_inl [(L.Sum L').Structure M] [(Lhom.sumInl : L →ᴸ L.Sum L').IsExpansionOn M] {n} {f : L.Functions n}
    {x : Finₓ n → M} : @funMap (L.Sum L') M _ n (Sum.inl f) x = funMap f x :=
  (Lhom.sumInl : L →ᴸ L.Sum L').map_on_function f x

@[simp]
theorem fun_map_sum_inr [(L'.Sum L).Structure M] [(Lhom.sumInr : L →ᴸ L'.Sum L).IsExpansionOn M] {n} {f : L.Functions n}
    {x : Finₓ n → M} : @funMap (L'.Sum L) M _ n (Sum.inr f) x = funMap f x :=
  (Lhom.sumInr : L →ᴸ L'.Sum L).map_on_function f x

instance (priority := 100) is_expansion_on_reduct (ϕ : L →ᴸ L') (M : Type _) [L'.Structure M] :
    @IsExpansionOn L L' ϕ M (ϕ.reduct M) _ := by
  letI := ϕ.reduct M
  exact ⟨fun _ f _ => rfl, fun _ R _ => rfl⟩

end Lhom

/-- A language equivalence maps the symbols of one language to symbols of another bijectively. -/
structure Lequiv (L L' : Language) where
  toLhom : L →ᴸ L'
  invLhom : L' →ᴸ L
  left_inv : inv_Lhom.comp to_Lhom = Lhom.id L
  right_inv : to_Lhom.comp inv_Lhom = Lhom.id L'

-- mathport name: «expr ≃ᴸ »
infixl:10 " ≃ᴸ " => Lequiv

-- \^L
namespace Lequiv

variable (L)

/-- The identity equivalence from a first-order language to itself. -/
@[simps]
protected def refl : L ≃ᴸ L :=
  ⟨Lhom.id L, Lhom.id L, Lhom.id_comp _, Lhom.id_comp _⟩

variable {L}

instance : Inhabited (L ≃ᴸ L) :=
  ⟨Lequiv.refl L⟩

variable {L'' : Language} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps]
protected def symm : L' ≃ᴸ L :=
  ⟨e.invLhom, e.toLhom, e.right_inv, e.left_inv⟩

/-- The composition of equivalences of first-order languages. -/
@[simps, trans]
protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
  ⟨e'.toLhom.comp e.toLhom, e.invLhom.comp e'.invLhom, by
    rw [Lhom.comp_assoc, ← Lhom.comp_assoc e'.inv_Lhom, e'.left_inv, Lhom.id_comp, e.left_inv], by
    rw [Lhom.comp_assoc, ← Lhom.comp_assoc e.to_Lhom, e.right_inv, Lhom.id_comp, e'.right_inv]⟩

end Lequiv

section ConstantsOn

variable (α : Type u')

/-- A language with constants indexed by a type. -/
@[simp]
def constantsOn : Language.{u', 0} :=
  Language.mk₂ α Pempty Pempty Pempty Pempty

variable {α}

theorem constants_on_constants : (constantsOn α).Constants = α :=
  rfl

instance is_algebraic_constants_on : IsAlgebraic (constantsOn α) :=
  language.is_algebraic_mk₂

instance is_relational_constants_on [ie : IsEmpty α] : IsRelational (constantsOn α) :=
  language.is_relational_mk₂

instance is_empty_functions_constants_on_succ {n : ℕ} : IsEmpty ((constantsOn α).Functions (n + 1)) :=
  Nat.casesOn n Pempty.is_empty fun n => Nat.casesOn n Pempty.is_empty fun _ => Pempty.is_empty

theorem card_constants_on : (constantsOn α).card = # α := by
  simp

/-- Gives a `constants_on α` structure to a type by assigning each constant a value. -/
def constantsOn.structure (f : α → M) : (constantsOn α).Structure M :=
  Structure.mk₂ f Pempty.elimₓ Pempty.elimₓ Pempty.elimₓ Pempty.elimₓ

variable {β : Type v'}

/-- A map between index types induces a map between constant languages. -/
def Lhom.constantsOnMap (f : α → β) : constantsOn α →ᴸ constantsOn β :=
  Lhom.mk₂ f Pempty.elimₓ Pempty.elimₓ Pempty.elimₓ Pempty.elimₓ

theorem constants_on_map_is_expansion_on {f : α → β} {fα : α → M} {fβ : β → M} (h : fβ ∘ f = fα) :
    @Lhom.IsExpansionOn _ _ (Lhom.constantsOnMap f) M (constantsOn.structure fα) (constantsOn.structure fβ) := by
  letI := constants_on.Structure fα
  letI := constants_on.Structure fβ
  exact ⟨fun n => Nat.casesOn n (fun F x => (congr_fun h F : _)) fun n F => isEmptyElim F, fun _ R => isEmptyElim R⟩

end ConstantsOn

section WithConstants

variable (L)

section

variable (α : Type w')

/-- Extends a language with a constant for each element of a parameter set in `M`. -/
def withConstants : Language.{max u w', v} :=
  L.Sum (constantsOn α)

-- mathport name: «expr [[ ]]»
localized [FirstOrder] notation:95 L "[[" α "]]" => L.withConstants α

@[simp]
theorem card_with_constants : L[[α]].card = Cardinal.lift.{w'} L.card + Cardinal.lift.{max u v} (# α) := by
  rw [with_constants, card_sum, card_constants_on]

/-- The language map adding constants.  -/
@[simps]
def lhomWithConstants : L →ᴸ L[[α]] :=
  Lhom.sum_inl

variable {α}

/-- The constant symbol indexed by a particular element. -/
protected def con (a : α) : L[[α]].Constants :=
  Sum.inr a

variable {L} (α)

/-- Adds constants to a language map.  -/
def Lhom.addConstants {L' : Language} (φ : L →ᴸ L') : L[[α]] →ᴸ L'[[α]] :=
  φ.sum_map (Lhom.id _)

instance paramsStructure (A : Set α) : (constantsOn A).Structure α :=
  constantsOn.structure coe

variable (L) (α)

/-- The language map removing an empty constant set.  -/
@[simps]
def Lequiv.addEmptyConstants [ie : IsEmpty α] : L ≃ᴸ L[[α]] where
  toLhom := lhomWithConstants L α
  invLhom := Lhom.sumElim (Lhom.id L) (Lhom.ofIsEmpty (constantsOn α) L)
  left_inv := by
    rw [Lhom_with_constants, Lhom.sum_elim_comp_inl]
  right_inv := by
    simp only [← Lhom.comp_sum_elim, ← Lhom_with_constants, ← Lhom.comp_id]
    exact trans (congr rfl (Subsingleton.elimₓ _ _)) Lhom.sum_elim_inl_inr

variable {α} {β : Type _}

@[simp]
theorem with_constants_fun_map_sum_inl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {n}
    {f : L.Functions n} {x : Finₓ n → M} : @funMap (L[[α]]) M _ n (Sum.inl f) x = funMap f x :=
  (lhomWithConstants L α).map_on_function f x

@[simp]
theorem with_constants_rel_map_sum_inl [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {n}
    {R : L.Relations n} {x : Finₓ n → M} : @RelMap (L[[α]]) M _ n (Sum.inl R) x = RelMap R x :=
  (lhomWithConstants L α).map_on_relation R x

/-- The language map extending the constant set.  -/
def lhomWithConstantsMap (f : α → β) : L[[α]] →ᴸ L[[β]] :=
  Lhom.sumMap (Lhom.id L) (Lhom.constantsOnMap f)

@[simp]
theorem Lhom.map_constants_comp_sum_inl {f : α → β} :
    (L.lhomWithConstantsMap f).comp Lhom.sumInl = L.lhomWithConstants β := by
  ext n f R <;> rfl

end

open FirstOrder

instance constantsOnSelfStructure : (constantsOn M).Structure M :=
  constantsOn.structure id

instance withConstantsSelfStructure : L[[M]].Structure M :=
  Language.sumStructure _ _ M

instance with_constants_self_expansion : (lhomWithConstants L M).IsExpansionOn M :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

variable (α : Type _) [(constantsOn α).Structure M]

instance withConstantsStructure : L[[α]].Structure M :=
  Language.sumStructure _ _ _

instance with_constants_expansion : (L.lhomWithConstants α).IsExpansionOn M :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

instance add_empty_constants_is_expansion_on' : (Lequiv.addEmptyConstants L (∅ : Set M)).toLhom.IsExpansionOn M :=
  L.with_constants_expansion _

instance add_empty_constants_symm_is_expansion_on :
    (Lequiv.addEmptyConstants L (∅ : Set M)).symm.toLhom.IsExpansionOn M :=
  Lhom.sum_elim_is_expansion_on _ _ _

instance add_constants_expansion {L' : Language} [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    (φ.addConstants α).IsExpansionOn M :=
  Lhom.sum_map_is_expansion_on _ _ M

@[simp]
theorem with_constants_fun_map_sum_inr {a : α} {x : Finₓ 0 → M} :
    @funMap (L[[α]]) M _ 0 (Sum.inr a : L[[α]].Functions 0) x = L.con a := by
  rw [Unique.eq_default x]
  exact (Lhom.sum_inr : constants_on α →ᴸ L.sum _).map_on_function _ _

variable {α} (A : Set M)

@[simp]
theorem coe_con {a : A} : (L.con a : M) = a :=
  rfl

variable {A} {B : Set M} (h : A ⊆ B)

instance constants_on_map_inclusion_is_expansion_on : (Lhom.constantsOnMap (Set.inclusion h)).IsExpansionOn M :=
  constants_on_map_is_expansion_on rfl

instance map_constants_inclusion_is_expansion_on : (L.lhomWithConstantsMap (Set.inclusion h)).IsExpansionOn M :=
  Lhom.sum_map_is_expansion_on _ _ _

end WithConstants

end Language

end FirstOrder

