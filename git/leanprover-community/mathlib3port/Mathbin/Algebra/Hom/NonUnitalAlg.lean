/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Algebra.Basic

/-!
# Morphisms of non-unital algebras

This file defines morphisms between two types, each of which carries:
 * an addition,
 * an additive zero,
 * a multiplication,
 * a scalar action.

The multiplications are not assumed to be associative or unital, or even to be compatible with the
scalar actions. In a typical application, the operations will satisfy compatibility conditions
making them into algebras (albeit possibly non-associative and/or non-unital) but such conditions
are not required to make this definition.

This notion of morphism should be useful for any category of non-unital algebras. The motivating
application at the time it was introduced was to be able to state the adjunction property for
magma algebras. These are non-unital, non-associative algebras obtained by applying the
group-algebra construction except where we take a type carrying just `has_mul` instead of `group`.

For a plausible future application, one could take the non-unital algebra of compactly-supported
functions on a non-compact topological space. A proper map between a pair of such spaces
(contravariantly) induces a morphism between their algebras of compactly-supported functions which
will be a `non_unital_alg_hom`.

TODO: add `non_unital_alg_equiv` when needed.

## Main definitions

  * `non_unital_alg_hom`
  * `alg_hom.to_non_unital_alg_hom`

## Tags

non-unital, algebra, morphism
-/


universe u v w w₁ w₂ w₃

variable (R : Type u) (A : Type v) (B : Type w) (C : Type w₁)

/-- A morphism respecting addition, multiplication, and scalar multiplication. When these arise from
algebra structures, this is the same as a not-necessarily-unital morphism of algebras. -/
structure NonUnitalAlgHom [Monoidₓ R] [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A]
  [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B] extends A →+[R] B, A →ₙ* B

-- mathport name: «expr →ₙₐ »
infixr:25 " →ₙₐ " => NonUnitalAlgHom _

-- mathport name: «expr →ₙₐ[ ] »
notation:25 A " →ₙₐ[" R "] " B => NonUnitalAlgHom R A B

attribute [nolint doc_blame] NonUnitalAlgHom.toDistribMulActionHom

attribute [nolint doc_blame] NonUnitalAlgHom.toMulHom

namespace NonUnitalAlgHom

variable {R A B C} [Monoidₓ R]

variable [NonUnitalNonAssocSemiringₓ A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiringₓ B] [DistribMulAction R B]

variable [NonUnitalNonAssocSemiringₓ C] [DistribMulAction R C]

/-- see Note [function coercion] -/
instance : CoeFun (A →ₙₐ[R] B) fun _ => A → B :=
  ⟨toFun⟩

@[simp]
theorem to_fun_eq_coe (f : A →ₙₐ[R] B) : f.toFun = ⇑f :=
  rfl

initialize_simps_projections NonUnitalAlgHom (toFun → apply)

theorem coe_injective : @Function.Injective (A →ₙₐ[R] B) (A → B) coeFn := by
  rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩ <;> congr

@[ext]
theorem ext {f g : A →ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

theorem ext_iff {f g : A →ₙₐ[R] B} : f = g ↔ ∀ x, f x = g x :=
  ⟨by
    rintro rfl x
    rfl, ext⟩

theorem congr_fun {f g : A →ₙₐ[R] B} (h : f = g) (x : A) : f x = g x :=
  h ▸ rfl

@[simp]
theorem coe_mk (f : A → B) h₁ h₂ h₃ h₄ : ((⟨f, h₁, h₂, h₃, h₄⟩ : A →ₙₐ[R] B) : A → B) = f :=
  rfl

@[simp]
theorem mk_coe (f : A →ₙₐ[R] B) h₁ h₂ h₃ h₄ : (⟨f, h₁, h₂, h₃, h₄⟩ : A →ₙₐ[R] B) = f := by
  ext
  rfl

instance : Coe (A →ₙₐ[R] B) (A →+[R] B) :=
  ⟨toDistribMulActionHom⟩

instance : Coe (A →ₙₐ[R] B) (A →ₙ* B) :=
  ⟨toMulHom⟩

@[simp]
theorem to_distrib_mul_action_hom_eq_coe (f : A →ₙₐ[R] B) : f.toDistribMulActionHom = ↑f :=
  rfl

@[simp]
theorem to_mul_hom_eq_coe (f : A →ₙₐ[R] B) : f.toMulHom = ↑f :=
  rfl

@[simp, norm_cast]
theorem coe_to_distrib_mul_action_hom (f : A →ₙₐ[R] B) : ((f : A →+[R] B) : A → B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_mul_hom (f : A →ₙₐ[R] B) : ((f : A →ₙ* B) : A → B) = f :=
  rfl

theorem to_distrib_mul_action_hom_injective {f g : A →ₙₐ[R] B} (h : (f : A →+[R] B) = (g : A →+[R] B)) : f = g := by
  ext a
  exact DistribMulActionHom.congr_fun h a

theorem to_mul_hom_injective {f g : A →ₙₐ[R] B} (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g := by
  ext a
  exact MulHom.congr_fun h a

@[norm_cast]
theorem coe_distrib_mul_action_hom_mk (f : A →ₙₐ[R] B) h₁ h₂ h₃ h₄ :
    ((⟨f, h₁, h₂, h₃, h₄⟩ : A →ₙₐ[R] B) : A →+[R] B) = ⟨f, h₁, h₂, h₃⟩ := by
  ext
  rfl

@[norm_cast]
theorem coe_mul_hom_mk (f : A →ₙₐ[R] B) h₁ h₂ h₃ h₄ : ((⟨f, h₁, h₂, h₃, h₄⟩ : A →ₙₐ[R] B) : A →ₙ* B) = ⟨f, h₄⟩ := by
  ext
  rfl

@[simp]
theorem map_smul (f : A →ₙₐ[R] B) (c : R) (x : A) : f (c • x) = c • f x :=
  f.toDistribMulActionHom.map_smul c x

@[simp]
theorem map_add (f : A →ₙₐ[R] B) (x y : A) : f (x + y) = f x + f y :=
  f.toDistribMulActionHom.map_add x y

@[simp]
theorem map_mul (f : A →ₙₐ[R] B) (x y : A) : f (x * y) = f x * f y :=
  f.toMulHom.map_mul x y

@[simp]
theorem map_zero (f : A →ₙₐ[R] B) : f 0 = 0 :=
  f.toDistribMulActionHom.map_zero

instance : Zero (A →ₙₐ[R] B) :=
  ⟨{ (0 : A →+[R] B) with
      map_mul' := by
        simp }⟩

instance : One (A →ₙₐ[R] A) :=
  ⟨{ (1 : A →+[R] A) with
      map_mul' := by
        simp }⟩

@[simp]
theorem coe_zero : ((0 : A →ₙₐ[R] B) : A → B) = 0 :=
  rfl

@[simp]
theorem coe_one : ((1 : A →ₙₐ[R] A) : A → A) = id :=
  rfl

theorem zero_apply (a : A) : (0 : A →ₙₐ[R] B) a = 0 :=
  rfl

theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a :=
  rfl

instance : Inhabited (A →ₙₐ[R] B) :=
  ⟨0⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) : A →ₙₐ[R] C :=
  { (f : B →ₙ* C).comp (g : A →ₙ* B), (f : B →+[R] C).comp (g : A →+[R] B) with }

@[simp, norm_cast]
theorem coe_comp (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) : (f.comp g : A → C) = (f : B → C) ∘ (g : A → B) :=
  rfl

theorem comp_apply (f : B →ₙₐ[R] C) (g : A →ₙₐ[R] B) (x : A) : f.comp g x = f (g x) :=
  rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : A →ₙₐ[R] B) (g : B → A) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    B →ₙₐ[R] A :=
  { (f : A →ₙ* B).inverse g h₁ h₂, (f : A →+[R] B).inverse g h₁ h₂ with }

@[simp]
theorem coe_inverse (f : A →ₙₐ[R] B) (g : B → A) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (inverse f g h₁ h₂ : B → A) = g :=
  rfl

end NonUnitalAlgHom

namespace AlgHom

variable {R A B} [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A] [Algebra R B]

/-- A unital morphism of algebras is a `non_unital_alg_hom`. -/
def toNonUnitalAlgHom (f : A →ₐ[R] B) : A →ₙₐ[R] B :=
  { f with map_smul' := f.map_smul }

instance NonUnitalAlgHom.hasCoe : Coe (A →ₐ[R] B) (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

@[simp]
theorem to_non_unital_alg_hom_eq_coe (f : A →ₐ[R] B) : f.toNonUnitalAlgHom = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_non_unital_alg_hom (f : A →ₐ[R] B) : ((f : A →ₙₐ[R] B) : A → B) = f :=
  rfl

end AlgHom

