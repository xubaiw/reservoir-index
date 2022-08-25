/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathbin.Topology.Homotopy.Equiv
import Mathbin.CategoryTheory.Equivalence
import Mathbin.AlgebraicTopology.FundamentalGroupoid.Product

/-!
# Homotopic maps induce naturally isomorphic functors

## Main definitions

  - `fundamental_groupoid_functor.homotopic_maps_nat_iso H` The natural isomorphism
    between the induced functors `f : π(X) ⥤ π(Y)` and `g : π(X) ⥤ π(Y)`, given a homotopy
    `H : f ∼ g`

  - `fundamental_groupoid_functor.equiv_of_homotopy_equiv hequiv` The equivalence of the categories
    `π(X)` and `π(Y)` given a homotopy equivalence `hequiv : X ≃ₕ Y` between them.

## Implementation notes
  - In order to be more universe polymorphic, we define `continuous_map.homotopy.ulift_map`
  which lifts a homotopy from `I × X → Y` to `(Top.of ((ulift I) × X)) → Y`. This is because
  this construction uses `fundamental_groupoid_functor.prod_to_prod_Top` to convert between
  pairs of paths in I and X and the corresponding path after passing through a homotopy `H`.
  But `fundamental_groupoid_functor.prod_to_prod_Top` requires two spaces in the same universe.
-/


noncomputable section

universe u

open FundamentalGroupoid

open CategoryTheory

open FundamentalGroupoidFunctor

open FundamentalGroupoid

open UnitInterval

namespace UnitInterval

/-- The path 0 ⟶ 1 in I -/
def path01 : Path (0 : I) 1 where
  toFun := id
  source' := rfl
  target' := rfl

/-- The path 0 ⟶ 1 in ulift I -/
def upath01 : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where
  toFun := ULift.up
  source' := rfl
  target' := rfl

attribute [local instance] Path.Homotopic.setoid

/-- The homotopy path class of 0 → 1 in `ulift I` -/
def uhpath01 : @fromTop (Top.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTop (ULift.up 1) :=
  ⟦upath01⟧

end UnitInterval

namespace ContinuousMap.Homotopy

open UnitInterval (uhpath01)

attribute [local instance] Path.Homotopic.setoid

section Casts

/-- Abbreviation for `eq_to_hom` that accepts points in a topological space -/
abbrev hcast {X : Top} {x₀ x₁ : X} (hx : x₀ = x₁) : fromTop x₀ ⟶ fromTop x₁ :=
  eqToHom hx

@[simp]
theorem hcast_def {X : Top} {x₀ x₁ : X} (hx₀ : x₀ = x₁) : hcast hx₀ = eqToHom hx₀ :=
  rfl

variable {X₁ X₂ Y : Top.{u}} {f : C(X₁, Y)} {g : C(X₂, Y)} {x₀ x₁ : X₁} {x₂ x₃ : X₂} {p : Path x₀ x₁} {q : Path x₂ x₃}
  (hfg : ∀ t, f (p t) = g (q t))

include hfg

/-- If `f(p(t) = g(q(t))` for two paths `p` and `q`, then the induced path homotopy classes
`f(p)` and `g(p)` are the same as well, despite having a priori different types -/
theorem heq_path_of_eq_image : HEq ((πₘ f).map ⟦p⟧) ((πₘ g).map ⟦q⟧) := by
  simp only [map_eq, ← Path.Homotopic.map_lift]
  apply Path.Homotopic.hpath_hext
  exact hfg

private theorem start_path : f x₀ = g x₂ := by
  convert hfg 0 <;> simp only [Path.source]

private theorem end_path : f x₁ = g x₃ := by
  convert hfg 1 <;> simp only [Path.target]

theorem eq_path_of_eq_image : (πₘ f).map ⟦p⟧ = hcast (start_path hfg) ≫ (πₘ g).map ⟦q⟧ ≫ hcast (end_path hfg).symm := by
  rw [functor.conj_eq_to_hom_iff_heq]
  exact heq_path_of_eq_image hfg

end Casts

-- We let `X` and `Y` be spaces, and `f` and `g` be homotopic maps between them
variable {X Y : Top.{u}} {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) {x₀ x₁ : X} (p : fromTop x₀ ⟶ fromTop x₁)

/-!
These definitions set up the following diagram, for each path `p`:

            f(p)
        *--------*
        | \      |
    H₀  |   \ d  |  H₁
        |     \  |
        *--------*
            g(p)

Here, `H₀ = H.eval_at x₀` is the path from `f(x₀)` to `g(x₀)`,
and similarly for `H₁`. Similarly, `f(p)` denotes the
path in Y that the induced map `f` takes `p`, and similarly for `g(p)`.

Finally, `d`, the diagonal path, is H(0 ⟶ 1, p), the result of the induced `H` on
`path.homotopic.prod (0 ⟶ 1) p`, where `(0 ⟶ 1)` denotes the path from `0` to `1` in `I`.

It is clear that the diagram commutes (`H₀ ≫ g(p) = d = f(p) ≫ H₁`), but unfortunately,
many of the paths do not have defeq starting/ending points, so we end up needing some casting.
-/


/-- Interpret a homotopy `H : C(I × X, Y) as a map C(ulift I × X, Y) -/
def uliftMap : C(Top.of (ULift.{u} I × X), Y) :=
  ⟨fun x => H (x.1.down, x.2), H.Continuous.comp ((continuous_induced_dom.comp continuous_fst).prod_mk continuous_snd)⟩

@[simp]
theorem ulift_apply (i : ULift.{u} I) (x : X) : H.uliftMap (i, x) = H (i.down, x) :=
  rfl

/-- An abbreviation for `prod_to_prod_Top`, with some types already in place to help the
 typechecker. In particular, the first path should be on the ulifted unit interval. -/
abbrev prodToProdTopI {a₁ a₂ : Top.of (ULift I)} {b₁ b₂ : X} (p₁ : fromTop a₁ ⟶ fromTop a₂)
    (p₂ : fromTop b₁ ⟶ fromTop b₂) :=
  @CategoryTheory.Functor.map _ _ _ _ (prodToProdTop (Top.of <| ULift I) X) (a₁, b₁) (a₂, b₂) (p₁, p₂)

/-- The diagonal path `d` of a homotopy `H` on a path `p` -/
def diagonalPath : fromTop (H (0, x₀)) ⟶ fromTop (H (1, x₁)) :=
  (πₘ H.uliftMap).map (prodToProdTopI uhpath01 p)

/-- The diagonal path, but starting from `f x₀` and going to `g x₁` -/
def diagonalPath' : fromTop (f x₀) ⟶ fromTop (g x₁) :=
  hcast (H.apply_zero x₀).symm ≫ H.diagonalPath p ≫ hcast (H.apply_one x₁)

/-- Proof that `f(p) = H(0 ⟶ 0, p)`, with the appropriate casts -/
theorem apply_zero_path :
    (πₘ f).map p =
      hcast (H.apply_zero x₀).symm ≫
        (πₘ H.uliftMap).map (prodToProdTopI (𝟙 (ULift.up 0)) p) ≫ hcast (H.apply_zero x₁) :=
  by
  apply Quotientₓ.induction_on p
  intro p'
  apply @eq_path_of_eq_image _ _ _ _ H.ulift_map _ _ _ _ _ ((Path.refl (ULift.up _)).Prod p')
  simp

/-- Proof that `g(p) = H(1 ⟶ 1, p)`, with the appropriate casts -/
theorem apply_one_path :
    (πₘ g).map p =
      hcast (H.apply_one x₀).symm ≫ (πₘ H.uliftMap).map (prodToProdTopI (𝟙 (ULift.up 1)) p) ≫ hcast (H.apply_one x₁) :=
  by
  apply Quotientₓ.induction_on p
  intro p'
  apply @eq_path_of_eq_image _ _ _ _ H.ulift_map _ _ _ _ _ ((Path.refl (ULift.up _)).Prod p')
  simp

/-- Proof that `H.eval_at x = H(0 ⟶ 1, x ⟶ x)`, with the appropriate casts -/
theorem eval_at_eq (x : X) :
    ⟦H.evalAt x⟧ =
      hcast (H.apply_zero x).symm ≫
        (πₘ H.uliftMap).map (prodToProdTopI uhpath01 (𝟙 x)) ≫ hcast (H.apply_one x).symm.symm :=
  by
  dunfold prod_to_prod_Top_I uhpath01 hcast
  refine' (@functor.conj_eq_to_hom_iff_heq (πₓ Y) _ _ _ _ _ _ _ _ _).mpr _
  simp only [id_eq_path_refl, prod_to_prod_Top_map, Path.Homotopic.prod_lift, map_eq, ← Path.Homotopic.map_lift]
  apply Path.Homotopic.hpath_hext
  intro
  rfl

-- Finally, we show `d = f(p) ≫ H₁ = H₀ ≫ g(p)`
theorem eq_diag_path :
    (πₘ f).map p ≫ ⟦H.evalAt x₁⟧ = H.diagonalPath' p ∧
      (⟦H.evalAt x₀⟧ ≫ (πₘ g).map p : fromTop (f x₀) ⟶ fromTop (g x₁)) = H.diagonalPath' p :=
  by
  rw [H.apply_zero_path, H.apply_one_path, H.eval_at_eq, H.eval_at_eq]
  dunfold prod_to_prod_Top_I
  constructor <;>
    · slice_lhs 2 5 => simp [← CategoryTheory.Functor.map_comp]
      rfl
      

end ContinuousMap.Homotopy

namespace FundamentalGroupoidFunctor

open CategoryTheory

open FundamentalGroupoid

attribute [local instance] Path.Homotopic.setoid

variable {X Y : Top.{u}} {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)

/-- Given a homotopy H : f ∼ g, we have an associated natural isomorphism between the induced
functors `f` and `g` -/
def homotopicMapsNatIso : πₘ f ⟶ πₘ g where
  app := fun x => ⟦H.evalAt x⟧
  naturality' := fun x y p => by
    rw [(H.eq_diag_path p).1, (H.eq_diag_path p).2]

instance : IsIso (homotopicMapsNatIso H) := by
  apply nat_iso.is_iso_of_is_iso_app

open ContinuousMap

/-- Homotopy equivalent topological spaces have equivalent fundamental groupoids. -/
def equivOfHomotopyEquiv (hequiv : X ≃ₕ Y) : πₓ X ≌ πₓ Y := by
  apply equivalence.mk (πₘ hequiv.to_fun : πₓ X ⥤ πₓ Y) (πₘ hequiv.inv_fun : πₓ Y ⥤ πₓ X) <;>
    simp only [Groupoid.hom_to_functor, Groupoid.id_to_functor]
  · convert (as_iso (homotopic_maps_nat_iso hequiv.left_inv.some)).symm
    exacts[(π.map_id X).symm, (π.map_comp _ _).symm]
    
  · convert as_iso (homotopic_maps_nat_iso hequiv.right_inv.some)
    exacts[(π.map_comp _ _).symm, (π.map_id Y).symm]
    

end FundamentalGroupoidFunctor

