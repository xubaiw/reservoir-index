/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathbin.Topology.Algebra.Module.Basic

/-!
# Weak dual topology

This file defines the weak-* topology on duals of suitable topological modules `E` over suitable
topological semirings `𝕜`. The (weak) dual consists of continuous linear functionals `E →L[𝕜] 𝕜`
from `E` to scalars `𝕜`. The weak-* topology is the coarsest topology on this dual
`weak_dual 𝕜 E := (E →L[𝕜] 𝕜)` w.r.t. which the evaluation maps at all `z : E` are continuous.

The weak dual is a module over `𝕜` if the semiring `𝕜` is commutative.

## Main definitions

The main definitions are the type `weak_dual 𝕜 E` and a topology instance on it.

* `weak_dual 𝕜 E` is a type synonym for `dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `weak_dual.topological_space` is the weak-* topology on `weak_dual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.

## Main results

We establish that `weak_dual 𝕜 E` has the following structure:
* `weak_dual.has_continuous_add`: The addition in `weak_dual 𝕜 E` is continuous.
* `weak_dual.module`: If the scalars `𝕜` are a commutative semiring, then `weak_dual 𝕜 E` is a
  module over `𝕜`.
* `weak_dual.has_continuous_smul`: If the scalars `𝕜` are a commutative semiring, then the scalar
  multiplication by `𝕜` in `weak_dual 𝕜 E` is continuous.

We prove the following results characterizing the weak-* topology:
* `weak_dual.eval_continuous`: For any `z : E`, the evaluation mapping `weak_dual 𝕜 E → 𝕜` taking
  `x'`to `x' z` is continuous.
* `weak_dual.continuous_of_continuous_eval`: For a mapping to `weak_dual 𝕜 E` to be continuous,
  it suffices that its compositions with evaluations at all points `z : E` are continuous.
* `weak_dual.tendsto_iff_forall_eval_tendsto`: Convergence in `weak_dual 𝕜 E` can be characterized
  in terms of convergence of the evaluations at all points `z : E`.

## Notations

No new notation is introduced.

## Implementation notes

The weak-* topology is defined as the induced topology under the mapping that associates to a dual
element `x'` the functional `E → 𝕜`, when the space `E → 𝕜` of functionals is equipped with the
topology of pointwise convergence (product topology).

Typically one might assume that `𝕜` is a topological semiring in the sense of the typeclasses
`topological_space 𝕜`, `semiring 𝕜`, `has_continuous_add 𝕜`, `has_continuous_mul 𝕜`,
and that the space `E` is a topological module over `𝕜` in the sense of the typeclasses
`topological_space E`, `add_comm_monoid E`, `has_continuous_add E`, `module 𝕜 E`,
`has_continuous_smul 𝕜 E`. The definitions and results are, however, given with weaker assumptions
when possible.

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology

## Tags

weak-star, weak dual

-/


noncomputable section

open Filter

open_locale TopologicalSpace

universe u v

section WeakStarTopology

/-!
### Weak star topology on duals of topological modules
-/


variable (𝕜 : Type _) [TopologicalSpace 𝕜] [Semiringₓ 𝕜]

variable (E : Type _) [TopologicalSpace E] [AddCommMonoidₓ E] [Module 𝕜 E]

-- ././Mathport/Syntax/Translate/Basic.lean:980:9: unsupported derive handler λ α, has_coe_to_fun α (λ _, E → 𝕜)
/-- The weak dual of a topological module `E` over a topological semiring `𝕜` consists of
continuous linear functionals from `E` to scalars `𝕜`. It is a type synonym with the usual dual
(when the latter is defined), but will be equipped with a different topology. -/
def WeakDual :=
  E →L[𝕜] 𝕜 deriving Inhabited, [anonymous]

instance [HasContinuousAdd 𝕜] : AddCommMonoidₓ (WeakDual 𝕜 E) :=
  ContinuousLinearMap.addCommMonoid

namespace WeakDual

/-- The weak-* topology instance `weak_dual.topological_space` on the dual of a topological module
`E` over a topological semiring `𝕜` is defined as the induced topology under the mapping that
associates to a dual element `x' : weak_dual 𝕜 E` the functional `E → 𝕜`, when the space `E → 𝕜`
of functionals is equipped with the topology of pointwise convergence (product topology). -/
instance : TopologicalSpace (WeakDual 𝕜 E) :=
  TopologicalSpace.induced (fun x' : WeakDual 𝕜 E => fun z : E => x' z) Pi.topologicalSpace

/-- The coercion `coe_fn : weak_dual 𝕜 E → (E → 𝕜)` is an embedding. -/
theorem coe_fn_embedding : Embedding (coeFn : WeakDual 𝕜 E → E → 𝕜) := by
  convert continuous_linear_map.coe_fn_injective.embedding_induced

theorem coe_fn_continuous : Continuous fun x' : WeakDual 𝕜 E => fun z : E => x' z :=
  continuous_induced_dom

theorem eval_continuous (z : E) : Continuous fun x' : WeakDual 𝕜 E => x' z :=
  (continuous_pi_iff.mp (coe_fn_continuous 𝕜 E)) z

theorem continuous_of_continuous_eval {α : Type u} [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ z, Continuous fun a => g a z) : Continuous g :=
  continuous_induced_rng (continuous_pi_iff.mpr h)

theorem tendsto_iff_forall_eval_tendsto {γ : Type u} {F : Filter γ} {ψs : γ → WeakDual 𝕜 E} {ψ : WeakDual 𝕜 E} :
    Tendsto ψs F (𝓝 ψ) ↔ ∀ z : E, Tendsto (fun i => ψs i z) F (𝓝 (ψ z)) := by
  rw [← tendsto_pi_nhds, (coe_fn_embedding 𝕜 E).tendsto_nhds_iff]

/-- Addition in `weak_dual 𝕜 E` is continuous. -/
instance [HasContinuousAdd 𝕜] : HasContinuousAdd (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng <|
      ((coe_fn_continuous 𝕜 E).comp continuous_fst).add ((coe_fn_continuous 𝕜 E).comp continuous_snd)⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `weak_dual 𝕜 E`. -/
instance (M : Type _) [Monoidₓ M] [DistribMulAction M 𝕜] [SmulCommClass 𝕜 M 𝕜] [HasContinuousConstSmul M 𝕜] :
    MulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.mulAction

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `weak_dual 𝕜 E`. -/
instance (M : Type _) [Monoidₓ M] [DistribMulAction M 𝕜] [SmulCommClass 𝕜 M 𝕜] [HasContinuousConstSmul M 𝕜]
    [HasContinuousAdd 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.distribMulAction

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `weak_dual 𝕜 E` is a module over `R`. -/
instance (R : Type _) [Semiringₓ R] [Module R 𝕜] [SmulCommClass 𝕜 R 𝕜] [HasContinuousConstSmul R 𝕜]
    [HasContinuousAdd 𝕜] : Module R (WeakDual 𝕜 E) :=
  ContinuousLinearMap.module

instance (M : Type _) [Monoidₓ M] [DistribMulAction M 𝕜] [SmulCommClass 𝕜 M 𝕜] [HasContinuousConstSmul M 𝕜] :
    HasContinuousConstSmul M (WeakDual 𝕜 E) :=
  ⟨fun m => continuous_induced_rng <| (coe_fn_continuous 𝕜 E).const_smul m⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `weak_dual 𝕜 E`. -/
instance (M : Type _) [Monoidₓ M] [DistribMulAction M 𝕜] [SmulCommClass 𝕜 M 𝕜] [TopologicalSpace M]
    [HasContinuousSmul M 𝕜] : HasContinuousSmul M (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng <| continuous_fst.smul ((coe_fn_continuous 𝕜 E).comp continuous_snd)⟩

end WeakDual

end WeakStarTopology

