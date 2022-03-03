/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.Topology.Opens
import Mathbin.CategoryTheory.Sites.Grothendieck
import Mathbin.CategoryTheory.Sites.Pretopology
import Mathbin.CategoryTheory.Limits.Lattice

/-!
# Grothendieck topology on a topological space

Define the Grothendieck topology and the pretopology associated to a topological space, and show
that the pretopology induces the topology.

The covering (pre)sieves on `X` are those for which the union of domains contains `X`.

## Tags

site, Grothendieck topology, space

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We define the two separately, rather than defining the Grothendieck topology as that generated
by the pretopology for the purpose of having nice definitional properties for the sieves.
-/


universe u

namespace Opens

variable (T : Type u) [TopologicalSpace T]

open CategoryTheory TopologicalSpace CategoryTheory.Limits

/-- The Grothendieck topology associated to a topological space. -/
def grothendieckTopology : GrothendieckTopology (Opens T) where
  Sieves := fun X S => ∀, ∀ x ∈ X, ∀, ∃ (U : _)(f : U ⟶ X), S f ∧ x ∈ U
  top_mem' := fun X x hx => ⟨_, 𝟙 _, trivialₓ, hx⟩
  pullback_stable' := fun X Y S f hf y hy => by
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩
    refine' ⟨U⊓Y, hom_of_le inf_le_right, _, hU, hy⟩
    apply S.downward_closed hg (hom_of_le inf_le_left)
  transitive' := fun X S hS R hR x hx => by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩
    exact ⟨_, g ≫ f, hg, hV⟩

/-- The Grothendieck pretopology associated to a topological space. -/
def pretopology : Pretopology (Opens T) where
  Coverings := fun X R => ∀, ∀ x ∈ X, ∀, ∃ (U : _)(f : U ⟶ X), R f ∧ x ∈ U
  has_isos := fun X Y f i x hx => ⟨_, _, presieve.singleton_self _, (inv f).le hx⟩
  pullbacks := fun X Y f S hS x hx => by
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩
    refine' ⟨_, _, presieve.pullback_arrows.mk _ _ hg, _⟩
    have : U⊓Y ≤ pullback g f
    refine' le_of_hom (pullback.lift (hom_of_le inf_le_left) (hom_of_le inf_le_right) rfl)
    apply this ⟨hU, hx⟩
  Transitive := fun X S Ti hS hTi x hx => by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩

/-- The pretopology associated to a space is the largest pretopology that
    generates the Grothendieck topology associated to the space. -/
@[simp]
theorem pretopology_of_grothendieck :
    Pretopology.ofGrothendieck _ (Opens.grothendieckTopology T) = Opens.pretopology T := by
  apply le_antisymmₓ
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, ⟨V, g₁, g₂, hg₂, _⟩, hU⟩
    exact ⟨V, g₂, hg₂, g₁.le hU⟩
    
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, hf, hU⟩
    exact ⟨U, f, sieve.le_generate R U hf, hU⟩
    

/-- The pretopology associated to a space induces the Grothendieck topology associated to the space.
-/
@[simp]
theorem pretopology_to_grothendieck :
    Pretopology.toGrothendieck _ (Opens.pretopology T) = Opens.grothendieckTopology T := by
  rw [← pretopology_of_grothendieck]
  apply (pretopology.gi (opens T)).l_u_eq

end Opens

