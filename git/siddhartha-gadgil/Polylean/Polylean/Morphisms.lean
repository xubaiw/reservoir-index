import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic

/-
It appears that mathlib4 does not yet have homomorphisms. We need:

* Homomorophisms for Abelian (additive) groups.
* Homomorophisms for rings.

As with all structures, there should be a typeclass for _being a morphism_ and theorems that let us access the defining properties of a morphism.
-/

-- @[to_additive]
class Group.Homomorphism {G H : Type _} [Group G] [Group H] (ϕ : G → H) where
  mul_dist : ∀ g g' : G, ϕ (g * g') = (ϕ g) * (ϕ g')


section Group

theorem Group.mul_left_cancel {G : Type _} [Group G] {a b c : G} : a * b = a * c → b = c := by
  intro h
  have : b = a⁻¹ * (a * b) := by simp
  simp [h] at this
  assumption

instance {G : Type _} [Group G] : IsMulLeftCancel G := ⟨@Group.mul_left_cancel G _⟩

theorem Group.mul_right_cancel {G : Type _} [Group G] {a b c : G} : b * a = c * a → b = c := by
  intro h
  have : b = (b * a) * a⁻¹ := by simp
  simp [h] at this
  assumption

instance {G : Type _} [Group G] : IsMulRightCancel G := ⟨@Group.mul_right_cancel G _⟩

@[simp] theorem one_inv {G : Type _} [Group G] : (1 : G)⁻¹ = 1 := by
  have : (1 : G)⁻¹ * 1 = 1 := mul_left_inv 1
  rw [mul_one] at this
  assumption

end Group


namespace Group.Homomorphism

variable {G H : Type _} [GrpG : Group G] [GrpH : Group H]
variable {ϕ : G → H} [Homϕ : Group.Homomorphism ϕ]


@[simp] theorem mul_distrib {g g' : G} : ϕ (g * g') = ϕ g * ϕ g' := Homomorphism.mul_dist g g'

/- Kernel of a group homomorphism-/
def kernel (ϕ : G → H) [Group.Homomorphism ϕ] := {g : G // ϕ g = 1}

@[simp] theorem one_image : ϕ 1 = 1 := by
  have : (ϕ 1) * (ϕ 1) = (ϕ 1) * 1 := by rw [← Homomorphism.mul_distrib, mul_one, mul_one]
  exact mul_left_cancel this

theorem hom_inv {g : G} : (ϕ g)⁻¹ = ϕ g⁻¹ := by
  have : ϕ g * ϕ g⁻¹ = ϕ g * (ϕ g)⁻¹ := by rw [← Homomorphism.mul_distrib]; simp
  exact GrpH.mul_left_cancel (Eq.symm this)

theorem inv_kernel {g : G} : ϕ g = 1 → ϕ g⁻¹ = 1 := by
  intro h
  have : ϕ g * ϕ g⁻¹ = 1 := by have := (mul_right_inv (ϕ g)); rw [hom_inv] at this; assumption
  rw [h, one_mul] at this
  assumption

theorem Kernel.eq_of_val_eq (ϕ : G → H) [Group.Homomorphism ϕ] : ∀ {g h : kernel ϕ}, Eq g.val h.val → Eq g h
  | ⟨v, h⟩, ⟨_, _⟩, rfl => rfl

instance : Group (kernel ϕ) :=
  {
    mul := λ ⟨g₁, prf₁⟩ ⟨g₂, prf₂⟩ => ⟨g₁ * g₂, by rw [Homϕ.mul_dist g₁ g₂, prf₁, prf₂, mul_one]⟩
    mul_assoc := λ ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => by 
      apply Kernel.eq_of_val_eq
      apply mul_assoc

    one := ⟨1, one_image⟩
    mul_one := by intro ⟨a, prf⟩; apply Kernel.eq_of_val_eq; apply mul_one
    one_mul := by intro ⟨a, prf⟩; apply Kernel.eq_of_val_eq; apply one_mul

    inv := λ ⟨g, prf⟩ => ⟨g⁻¹, inv_kernel prf⟩
    mul_left_inv := by 
          intro ⟨a, prf⟩; apply Kernel.eq_of_val_eq; simp [Inv.inv]; 
          apply mul_left_inv

    npow_zero' := by intros; rfl
    npow_succ' := by intros; rfl

    div_eq_mul_inv := by intros; rfl
    gpow_zero' := by intros; rfl
    gpow_succ' := by intros; rfl
    gpow_neg' := by intros; rfl
  }

end Group.Homomorphism

section

variable {G : Type _} [Grp : Group G]

def subType (P: G → Prop) := {g : G // P g}

theorem Subgroup.eq_of_val_eq (P : G → Prop)  : 
    ∀ {g h : subType P}, Eq g.val h.val → Eq g h
  | ⟨v, h⟩, ⟨_, _⟩, rfl => rfl

instance (P : G → Prop)
  (mul_closure : ∀ {a b : G}, P a → P b → P (a * b))
  (inv_closure : ∀ {a : G}, P a → P a⁻¹)
  (id_closure : P 1) :
  Group {g : G // P g} :=
   {
    mul := λ ⟨g₁, prf₁⟩ ⟨g₂, prf₂⟩ => ⟨g₁ * g₂, mul_closure prf₁ prf₂⟩
    mul_assoc := λ ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => by
      apply Subgroup.eq_of_val_eq; apply mul_assoc

    one := ⟨1, id_closure⟩
    mul_one := by intro α 
                  apply Subgroup.eq_of_val_eq
                  apply mul_one 
    one_mul := by intro α 
                  apply Subgroup.eq_of_val_eq
                  apply one_mul

    inv := λ ⟨g, prf⟩ => ⟨g⁻¹, inv_closure prf⟩
    mul_left_inv := by 
                        intro ⟨a, prf⟩
                        simp [Inv.inv]
                        apply Subgroup.eq_of_val_eq
                        apply mul_left_inv

    npow_zero' := by intros; rfl
    npow_succ' := by intros; rfl

    div_eq_mul_inv := by intros; rfl
    gpow_zero' := by intros; rfl
    gpow_succ' := by intros; rfl
    gpow_neg' := by intros; rfl
  }

end

section Morphisms

class AddCommGroup.Homomorphism {A B : Type _} [AddCommGroup A] [AddCommGroup B] (ϕ : A → B) where
  add_dist : ∀ a a' : A, ϕ (a + a') = ϕ a + ϕ a'

class Monoid.Homomorphism {M N : Type _} [Monoid M] [Monoid N] (ϕ : M → N) where
  mul_dist : ∀ m m' : M, ϕ (m * m') = ϕ m * ϕ m'
  one_map : ϕ 1 = 1

class CommRing.Homomorphism {R S : Type _} [CommRing R] [CommRing S] (ϕ : R → S)
  extends AddCommGroup.Homomorphism ϕ, Monoid.Homomorphism ϕ


instance {A B C : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
         (ϕ : A → B) [AddCommGroup.Homomorphism ϕ] (ψ : B → C) [AddCommGroup.Homomorphism ψ] :
         AddCommGroup.Homomorphism (ψ ∘ ϕ) where
  add_dist := by intros; simp [AddCommGroup.Homomorphism.add_dist]

instance {L M N : Type _} [Monoid L] [Monoid M] [Monoid N]
         (ϕ : L → M) [Monoid.Homomorphism ϕ] (ψ : M → N) [Monoid.Homomorphism ψ] :
         Monoid.Homomorphism (ψ ∘ ϕ) where
  mul_dist := by intros; simp [Monoid.Homomorphism.mul_dist]
  one_map := by simp [Monoid.Homomorphism.one_map]


instance {A : Type _} [AddCommGroup A] : AddCommGroup.Homomorphism (id : A → A) where
  add_dist := by intros; rfl

instance {M : Type _} [Monoid M] : Monoid.Homomorphism (id : M → M) where
  mul_dist := by intros; rfl
  one_map := by rfl

end Morphisms

section AddCommGroup.Homomorphism

variable {A B : Type _} [α : AddCommGroup A] [β : AddCommGroup B]
variable (ϕ : A → B) [abg : AddCommGroup.Homomorphism ϕ]

theorem add_dist : ∀ a a' : A, ϕ (a + a') = ϕ a + ϕ a' := abg.add_dist

theorem zero_image : ϕ (0 : A) = (0 : B) := by
  have : ϕ 0 + ϕ 0 = ϕ 0 + 0 := by rw [← add_dist, add_zero, add_zero]
  exact add_left_cancel this

theorem neg_push : ∀ a : A, ϕ (-a) = -ϕ a := by
  intro a
  have : ϕ a + ϕ (-a) = ϕ a + - ϕ a := by rw [← add_dist, add_right_neg, add_right_neg, zero_image ϕ]
  exact add_left_cancel this

theorem nsmul_hom : ∀ n : ℕ, ∀ a b : A, nsmul_rec n (a + b) = nsmul_rec n a + nsmul_rec n b := by
  intros n a b
  cases n
  · simp [nsmul_rec]
  · simp [nsmul_rec]
    rw [add_assoc, add_assoc, add_left_cancel_iff, ← add_assoc, add_comm (nsmul_rec _ a) _, add_assoc, add_left_cancel_iff]
    exact nsmul_hom _ a b

theorem gsmul_hom : ∀ n : ℤ, ∀ a b : A, gsmul_rec n (a + b) = gsmul_rec n a + gsmul_rec n b := by
  intros n a b
  cases n
  · simp [gsmul_rec]; exact nsmul_hom _ a b
  · simp [gsmul_rec]; apply neg_eq_of_add_eq_zero
    rw [nsmul_hom _ a b, add_assoc, add_comm (nsmul_rec _ b) _, ← add_assoc, ← add_assoc, add_right_neg, zero_add, add_left_neg]

instance {n : ℤ} : AddCommGroup.Homomorphism (gsmul_rec n : A → A) where
  add_dist := gsmul_hom n

theorem neg_hom : ∀ a a' : A, -(a + a') = -a + -a' := by
  intro a a'
  rw [← @add_left_cancel_iff _ _ _ a _ _, ← @add_left_cancel_iff _ _ _ a' _ _, ← add_assoc a (-a) _, add_right_neg, zero_add, add_right_neg,
  ← add_assoc, add_comm a a', add_right_neg]

def neg (a : A) := -a

instance : AddCommGroup.Homomorphism (neg : A → A) where
  add_dist := neg_hom

instance : AddCommGroup.Homomorphism (id : A → A) where
  add_dist := λ _ _ => rfl

end AddCommGroup.Homomorphism
