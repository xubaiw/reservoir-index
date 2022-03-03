/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.Data.Equiv.MulAdd
import Mathbin.Algebra.Field.Basic
import Mathbin.Algebra.Ring.Opposite
import Mathbin.Algebra.BigOperators.Basic

/-!
# (Semi)ring equivs

In this file we define extension of `equiv` called `ring_equiv`, which is a datatype representing an
isomorphism of `semiring`s, `ring`s, `division_ring`s, or `field`s. We also introduce the
corresponding group of automorphisms `ring_aut`.

## Notations

* ``infix ` ≃+* `:25 := ring_equiv``

The extended equiv have coercions to functions, and the coercion is the canonical notation when
treating the isomorphism as maps.

## Implementation notes

The fields for `ring_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as these are
deprecated.

Definition of multiplication in the groups of automorphisms agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, not with
`category_theory.comp`.

## Tags

equiv, mul_equiv, add_equiv, ring_equiv, mul_aut, add_aut, ring_aut
-/


open_locale BigOperators

variable {R : Type _} {S : Type _} {S' : Type _}

/-- An equivalence between two (semi)rings that preserves the algebraic structure. -/
structure RingEquiv (R S : Type _) [Mul R] [Add R] [Mul S] [Add S] extends R ≃ S, R ≃* S, R ≃+ S

-- mathport name: «expr ≃+* »
infixl:25 " ≃+* " => RingEquiv

/-- The "plain" equivalence of types underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toEquiv

/-- The equivalence of additive monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toAddEquiv

/-- The equivalence of multiplicative monoids underlying an equivalence of (semi)rings. -/
add_decl_doc RingEquiv.toMulEquiv

/-- `ring_equiv_class F R S` states that `F` is a type of ring structure preserving equivalences.
You should extend this class when you extend `ring_equiv`. -/
class RingEquivClass (F : Type _) (R S : outParam (Type _)) [Mul R] [Add R] [Mul S] [Add S] extends
  MulEquivClass F R S where
  map_add : ∀ f : F a b, f (a + b) = f a + f b

namespace RingEquivClass

-- See note [lower instance priority]
instance (priority := 100) toAddEquivClass (F R S : Type _) [Mul R] [Add R] [Mul S] [Add S] [h : RingEquivClass F R S] :
    AddEquivClass F R S :=
  { h with coe := coeFn }

-- See note [lower instance priority]
instance (priority := 100) toRingHomClass (F R S : Type _) [NonAssocSemiringₓ R] [NonAssocSemiringₓ S]
    [h : RingEquivClass F R S] : RingHomClass F R S :=
  { h with coe := coeFn, coe_injective' := FunLike.coe_injective, map_zero := map_zero, map_one := map_one }

end RingEquivClass

namespace RingEquiv

section Basic

variable [Mul R] [Add R] [Mul S] [Add S] [Mul S'] [Add S']

instance : RingEquivClass (R ≃+* S) R S where
  coe := toFun
  inv := invFun
  coe_injective' := fun e f h₁ h₂ => by
    cases e
    cases f
    congr
  map_add := map_add'
  map_mul := map_mul'
  left_inv := RingEquiv.left_inv
  right_inv := RingEquiv.right_inv

instance : CoeFun (R ≃+* S) fun _ => R → S :=
  ⟨RingEquiv.toFun⟩

@[simp]
theorem to_fun_eq_coe (f : R ≃+* S) : f.toFun = f :=
  rfl

/-- A ring isomorphism preserves multiplication. -/
protected theorem map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y :=
  map_mul e x y

/-- A ring isomorphism preserves addition. -/
protected theorem map_add (e : R ≃+* S) (x y : R) : e (x + y) = e x + e y :=
  map_add e x y

/-- Two ring isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext]
theorem ext {f g : R ≃+* S} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

@[simp]
theorem coe_mk e e' h₁ h₂ h₃ h₄ : ⇑(⟨e, e', h₁, h₂, h₃, h₄⟩ : R ≃+* S) = e :=
  rfl

@[simp]
theorem mk_coe (e : R ≃+* S) e' h₁ h₂ h₃ h₄ : (⟨e, e', h₁, h₂, h₃, h₄⟩ : R ≃+* S) = e :=
  ext fun _ => rfl

protected theorem congr_arg {f : R ≃+* S} {x x' : R} : x = x' → f x = f x' :=
  FunLike.congr_arg f

protected theorem congr_fun {f g : R ≃+* S} (h : f = g) (x : R) : f x = g x :=
  FunLike.congr_fun h x

protected theorem ext_iff {f g : R ≃+* S} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

instance hasCoeToMulEquiv : Coe (R ≃+* S) (R ≃* S) :=
  ⟨RingEquiv.toMulEquiv⟩

instance hasCoeToAddEquiv : Coe (R ≃+* S) (R ≃+ S) :=
  ⟨RingEquiv.toAddEquiv⟩

@[simp]
theorem to_add_equiv_eq_coe (f : R ≃+* S) : f.toAddEquiv = ↑f :=
  rfl

@[simp]
theorem to_mul_equiv_eq_coe (f : R ≃+* S) : f.toMulEquiv = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_to_mul_equiv (f : R ≃+* S) : ⇑(f : R ≃* S) = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_add_equiv (f : R ≃+* S) : ⇑(f : R ≃+ S) = f :=
  rfl

/-- The `ring_equiv` between two semirings with a unique element. -/
def ringEquivOfUniqueOfUnique {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : M ≃+* N :=
  { AddEquiv.addEquivOfUniqueOfUnique, MulEquiv.mulEquivOfUniqueOfUnique with }

instance {M N} [Unique M] [Unique N] [Add M] [Mul M] [Add N] [Mul N] : Unique (M ≃+* N) where
  default := ringEquivOfUniqueOfUnique
  uniq := fun _ => ext fun x => Subsingleton.elimₓ _ _

variable (R)

/-- The identity map is a ring isomorphism. -/
@[refl]
protected def refl : R ≃+* R :=
  { MulEquiv.refl R, AddEquiv.refl R with }

@[simp]
theorem refl_apply (x : R) : RingEquiv.refl R x = x :=
  rfl

@[simp]
theorem coe_add_equiv_refl : (RingEquiv.refl R : R ≃+ R) = AddEquiv.refl R :=
  rfl

@[simp]
theorem coe_mul_equiv_refl : (RingEquiv.refl R : R ≃* R) = MulEquiv.refl R :=
  rfl

instance : Inhabited (R ≃+* R) :=
  ⟨RingEquiv.refl R⟩

variable {R}

/-- The inverse of a ring isomorphism is a ring isomorphism. -/
@[symm]
protected def symm (e : R ≃+* S) : S ≃+* R :=
  { e.toMulEquiv.symm, e.toAddEquiv.symm with }

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : R ≃+* S) : S → R :=
  e.symm

initialize_simps_projections RingEquiv (toFun → apply, invFun → symmApply)

@[simp]
theorem inv_fun_eq_symm (f : R ≃+* S) : f.invFun = f.symm :=
  rfl

@[simp]
theorem symm_symm (e : R ≃+* S) : e.symm.symm = e :=
  ext fun x => rfl

theorem symm_bijective : Function.Bijective (RingEquiv.symm : R ≃+* S → S ≃+* R) :=
  Equivₓ.bijective ⟨RingEquiv.symm, RingEquiv.symm, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : R ≃+* S) f h₁ h₂ h₃ h₄ : (RingEquiv.mk f (⇑e) h₁ h₂ h₃ h₄ : S ≃+* R) = e.symm :=
  symm_bijective.Injective <| ext fun x => rfl

@[simp]
theorem symm_mk (f : R → S) g h₁ h₂ h₃ h₄ :
    (mk f g h₁ h₂ h₃ h₄).symm = { (mk f g h₁ h₂ h₃ h₄).symm with toFun := g, invFun := f } :=
  rfl

/-- Transitivity of `ring_equiv`. -/
@[trans]
protected def trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : R ≃+* S' :=
  { e₁.toMulEquiv.trans e₂.toMulEquiv, e₁.toAddEquiv.trans e₂.toAddEquiv with }

@[simp]
theorem trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e₁ a) :=
  rfl

protected theorem bijective (e : R ≃+* S) : Function.Bijective e :=
  EquivLike.bijective e

protected theorem injective (e : R ≃+* S) : Function.Injective e :=
  EquivLike.injective e

protected theorem surjective (e : R ≃+* S) : Function.Surjective e :=
  EquivLike.surjective e

@[simp]
theorem apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

theorem image_eq_preimage (e : R ≃+* S) (s : Set R) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s

end Basic

section Opposite

open MulOpposite

/-- A ring iso `α ≃+* β` can equivalently be viewed as a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. -/
@[simps]
protected def op {α β} [Add α] [Mul α] [Add β] [Mul β] : α ≃+* β ≃ (αᵐᵒᵖ ≃+* βᵐᵒᵖ) where
  toFun := fun f => { f.toAddEquiv.mulOp, f.toMulEquiv.op with }
  invFun := fun f => { AddEquiv.mulOp.symm f.toAddEquiv, MulEquiv.op.symm f.toMulEquiv with }
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    rfl

/-- The 'unopposite' of a ring iso `αᵐᵒᵖ ≃+* βᵐᵒᵖ`. Inverse to `ring_equiv.op`. -/
@[simp]
protected def unop {α β} [Add α] [Mul α] [Add β] [Mul β] : αᵐᵒᵖ ≃+* βᵐᵒᵖ ≃ (α ≃+* β) :=
  RingEquiv.op.symm

section CommSemiringₓ

variable (R) [CommSemiringₓ R]

/-- A commutative ring is isomorphic to its opposite. -/
def toOpposite : R ≃+* Rᵐᵒᵖ :=
  { MulOpposite.opEquiv with map_add' := fun x y => rfl, map_mul' := fun x y => mul_comm (op y) (op x) }

@[simp]
theorem to_opposite_apply (r : R) : toOpposite R r = op r :=
  rfl

@[simp]
theorem to_opposite_symm_apply (r : Rᵐᵒᵖ) : (toOpposite R).symm r = unop r :=
  rfl

end CommSemiringₓ

end Opposite

section NonUnitalSemiringₓ

variable [NonUnitalNonAssocSemiringₓ R] [NonUnitalNonAssocSemiringₓ S] (f : R ≃+* S) (x y : R)

/-- A ring isomorphism sends zero to zero. -/
protected theorem map_zero : f 0 = 0 :=
  map_zero f

variable {x}

protected theorem map_eq_zero_iff : f x = 0 ↔ x = 0 :=
  AddEquivClass.map_eq_zero_iff f

theorem map_ne_zero_iff : f x ≠ 0 ↔ x ≠ 0 :=
  AddEquivClass.map_ne_zero_iff f

end NonUnitalSemiringₓ

section Semiringₓ

variable [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] (f : R ≃+* S) (x y : R)

/-- A ring isomorphism sends one to one. -/
protected theorem map_one : f 1 = 1 :=
  map_one f

variable {x}

protected theorem map_eq_one_iff : f x = 1 ↔ x = 1 :=
  MulEquivClass.map_eq_one_iff f

theorem map_ne_one_iff : f x ≠ 1 ↔ x ≠ 1 :=
  MulEquivClass.map_ne_one_iff f

/-- Produce a ring isomorphism from a bijective ring homomorphism. -/
noncomputable def ofBijective (f : R →+* S) (hf : Function.Bijective f) : R ≃+* S :=
  { Equivₓ.ofBijective f hf, f with }

@[simp]
theorem coe_of_bijective (f : R →+* S) (hf : Function.Bijective f) : (ofBijective f hf : R → S) = f :=
  rfl

theorem of_bijective_apply (f : R →+* S) (hf : Function.Bijective f) (x : R) : ofBijective f hf x = f x :=
  rfl

/-- A family of ring isomorphisms `Π j, (R j ≃+* S j)` generates a
ring isomorphisms between `Π j, R j` and `Π j, S j`.

This is the `ring_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`ring_equiv.arrow_congr`.
-/
@[simps apply]
def piCongrRight {ι : Type _} {R S : ι → Type _} [∀ i, Semiringₓ (R i)] [∀ i, Semiringₓ (S i)] (e : ∀ i, R i ≃+* S i) :
    (∀ i, R i) ≃+* ∀ i, S i :=
  { @MulEquiv.piCongrRight ι R S _ _ fun i => (e i).toMulEquiv,
    @AddEquiv.piCongrRight ι R S _ _ fun i => (e i).toAddEquiv with toFun := fun x j => e j (x j),
    invFun := fun x j => (e j).symm (x j) }

@[simp]
theorem Pi_congr_right_refl {ι : Type _} {R : ι → Type _} [∀ i, Semiringₓ (R i)] :
    (piCongrRight fun i => RingEquiv.refl (R i)) = RingEquiv.refl _ :=
  rfl

@[simp]
theorem Pi_congr_right_symm {ι : Type _} {R S : ι → Type _} [∀ i, Semiringₓ (R i)] [∀ i, Semiringₓ (S i)]
    (e : ∀ i, R i ≃+* S i) : (piCongrRight e).symm = Pi_congr_right fun i => (e i).symm :=
  rfl

@[simp]
theorem Pi_congr_right_trans {ι : Type _} {R S T : ι → Type _} [∀ i, Semiringₓ (R i)] [∀ i, Semiringₓ (S i)]
    [∀ i, Semiringₓ (T i)] (e : ∀ i, R i ≃+* S i) (f : ∀ i, S i ≃+* T i) :
    (piCongrRight e).trans (piCongrRight f) = Pi_congr_right fun i => (e i).trans (f i) :=
  rfl

end Semiringₓ

section

variable [Ringₓ R] [Ringₓ S] (f : R ≃+* S) (x y : R)

protected theorem map_neg : f (-x) = -f x :=
  map_neg f x

protected theorem map_sub : f (x - y) = f x - f y :=
  map_sub f x y

@[simp]
theorem map_neg_one : f (-1) = -1 :=
  f.map_one ▸ f.map_neg 1

end

section SemiringHom

variable [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] [NonAssocSemiringₓ S']

/-- Reinterpret a ring equivalence as a ring homomorphism. -/
def toRingHom (e : R ≃+* S) : R →+* S :=
  { e.toMulEquiv.toMonoidHom, e.toAddEquiv.toAddMonoidHom with }

theorem to_ring_hom_injective : Function.Injective (toRingHom : R ≃+* S → R →+* S) := fun f g h =>
  RingEquiv.ext (RingHom.ext_iff.1 h)

instance hasCoeToRingHom : Coe (R ≃+* S) (R →+* S) :=
  ⟨RingEquiv.toRingHom⟩

theorem to_ring_hom_eq_coe (f : R ≃+* S) : f.toRingHom = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_to_ring_hom (f : R ≃+* S) : ⇑(f : R →+* S) = f :=
  rfl

theorem coe_ring_hom_inj_iff {R S : Type _} [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] (f g : R ≃+* S) :
    f = g ↔ (f : R →+* S) = g :=
  ⟨congr_argₓ _, fun h => ext <| RingHom.ext_iff.mp h⟩

/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
abbrev toMonoidHom (e : R ≃+* S) : R →* S :=
  e.toRingHom.toMonoidHom

/-- Reinterpret a ring equivalence as an `add_monoid` homomorphism. -/
abbrev toAddMonoidHom (e : R ≃+* S) : R →+ S :=
  e.toRingHom.toAddMonoidHom

/-- The two paths coercion can take to an `add_monoid_hom` are equivalent -/
theorem to_add_monoid_hom_commutes (f : R ≃+* S) : (f : R →+* S).toAddMonoidHom = (f : R ≃+ S).toAddMonoidHom :=
  rfl

/-- The two paths coercion can take to an `monoid_hom` are equivalent -/
theorem to_monoid_hom_commutes (f : R ≃+* S) : (f : R →+* S).toMonoidHom = (f : R ≃* S).toMonoidHom :=
  rfl

/-- The two paths coercion can take to an `equiv` are equivalent -/
theorem to_equiv_commutes (f : R ≃+* S) : (f : R ≃+ S).toEquiv = (f : R ≃* S).toEquiv :=
  rfl

@[simp]
theorem to_ring_hom_refl : (RingEquiv.refl R).toRingHom = RingHom.id R :=
  rfl

@[simp]
theorem to_monoid_hom_refl : (RingEquiv.refl R).toMonoidHom = MonoidHom.id R :=
  rfl

@[simp]
theorem to_add_monoid_hom_refl : (RingEquiv.refl R).toAddMonoidHom = AddMonoidHom.id R :=
  rfl

@[simp]
theorem to_ring_hom_apply_symm_to_ring_hom_apply (e : R ≃+* S) : ∀ y : S, e.toRingHom (e.symm.toRingHom y) = y :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_to_ring_hom_apply_to_ring_hom_apply (e : R ≃+* S) : ∀ x : R, e.symm.toRingHom (e.toRingHom x) = x :=
  Equivₓ.symm_apply_apply e.toEquiv

@[simp]
theorem to_ring_hom_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂).toRingHom = e₂.toRingHom.comp e₁.toRingHom :=
  rfl

@[simp]
theorem to_ring_hom_comp_symm_to_ring_hom (e : R ≃+* S) : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
  ext
  simp

@[simp]
theorem symm_to_ring_hom_comp_to_ring_hom (e : R ≃+* S) : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := by
  ext
  simp

/-- Construct an equivalence of rings from homomorphisms in both directions, which are inverses.
-/
def ofHomInv (hom : R →+* S) (inv : S →+* R) (hom_inv_id : inv.comp hom = RingHom.id R)
    (inv_hom_id : hom.comp inv = RingHom.id S) : R ≃+* S :=
  { hom with invFun := inv, left_inv := fun x => RingHom.congr_fun hom_inv_id x,
    right_inv := fun x => RingHom.congr_fun inv_hom_id x }

@[simp]
theorem of_hom_inv_apply (hom : R →+* S) (inv : S →+* R) hom_inv_id inv_hom_id (r : R) :
    (ofHomInv hom inv hom_inv_id inv_hom_id) r = hom r :=
  rfl

@[simp]
theorem of_hom_inv_symm_apply (hom : R →+* S) (inv : S →+* R) hom_inv_id inv_hom_id (s : S) :
    (ofHomInv hom inv hom_inv_id inv_hom_id).symm s = inv s :=
  rfl

end SemiringHom

section BigOperators

theorem map_list_prod [Semiringₓ R] [Semiringₓ S] (f : R ≃+* S) (l : List R) : f l.Prod = (l.map f).Prod :=
  f.toRingHom.map_list_prod l

theorem map_list_sum [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] (f : R ≃+* S) (l : List R) : f l.Sum = (l.map f).Sum :=
  f.toRingHom.map_list_sum l

/-- An isomorphism into the opposite ring acts on the product by acting on the reversed elements -/
theorem unop_map_list_prod [Semiringₓ R] [Semiringₓ S] (f : R ≃+* Sᵐᵒᵖ) (l : List R) :
    MulOpposite.unop (f l.Prod) = (l.map (MulOpposite.unop ∘ f)).reverse.Prod :=
  f.toRingHom.unop_map_list_prod l

theorem map_multiset_prod [CommSemiringₓ R] [CommSemiringₓ S] (f : R ≃+* S) (s : Multiset R) :
    f s.Prod = (s.map f).Prod :=
  f.toRingHom.map_multiset_prod s

theorem map_multiset_sum [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] (f : R ≃+* S) (s : Multiset R) :
    f s.Sum = (s.map f).Sum :=
  f.toRingHom.map_multiset_sum s

theorem map_prod {α : Type _} [CommSemiringₓ R] [CommSemiringₓ S] (g : R ≃+* S) (f : α → R) (s : Finset α) :
    g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  g.toRingHom.map_prod f s

theorem map_sum {α : Type _} [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] (g : R ≃+* S) (f : α → R) (s : Finset α) :
    g (∑ x in s, f x) = ∑ x in s, g (f x) :=
  g.toRingHom.map_sum f s

end BigOperators

section DivisionRing

variable {K K' : Type _} [DivisionRing K] [DivisionRing K'] (g : K ≃+* K') (x y : K)

theorem map_inv : g x⁻¹ = (g x)⁻¹ :=
  g.toRingHom.map_inv x

theorem map_div : g (x / y) = g x / g y :=
  g.toRingHom.map_div x y

end DivisionRing

section GroupPower

variable [Semiringₓ R] [Semiringₓ S]

protected theorem map_pow (f : R ≃+* S) a : ∀ n : ℕ, f (a ^ n) = f a ^ n :=
  map_pow f a

end GroupPower

end RingEquiv

namespace MulEquiv

/-- Gives a `ring_equiv` from a `mul_equiv` preserving addition.-/
def toRingEquiv {R : Type _} {S : Type _} [Add R] [Add S] [Mul R] [Mul S] (h : R ≃* S)
    (H : ∀ x y : R, h (x + y) = h x + h y) : R ≃+* S :=
  { h.toEquiv, h, AddEquiv.mk' h.toEquiv H with }

end MulEquiv

namespace RingEquiv

variable [Add R] [Add S] [Mul R] [Mul S]

@[simp]
theorem self_trans_symm (e : R ≃+* S) : e.trans e.symm = RingEquiv.refl R :=
  ext e.3

@[simp]
theorem symm_trans_self (e : R ≃+* S) : e.symm.trans e = RingEquiv.refl S :=
  ext e.4

/-- If two rings are isomorphic, and the second is a domain, then so is the first. -/
protected theorem is_domain {A : Type _} (B : Type _) [Ringₓ A] [Ringₓ B] [IsDomain B] (e : A ≃+* B) : IsDomain A :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := fun x y hxy => by
      have : e x * e y = 0 := by
        rw [← e.map_mul, hxy, e.map_zero]
      simpa using eq_zero_or_eq_zero_of_mul_eq_zero this,
    exists_pair_ne := ⟨e.symm 0, e.symm 1, e.symm.Injective.Ne zero_ne_one⟩ }

end RingEquiv

