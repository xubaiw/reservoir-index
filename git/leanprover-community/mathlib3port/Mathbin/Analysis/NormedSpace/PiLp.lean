/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.MeanInequalities

/-!
# `L^p` distance on finite products of metric spaces
Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a real parameter `p ∈ [1, ∞)`, that also induce
the product topology. We define them in this file. The distance on `Π i, α i` is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Pi type, named
`pi_Lp p α`. The assumpion `[fact (1 ≤ p)]` is required for the metric and normed space instances.

We ensure that the topology and uniform structure on `pi_Lp p α` are (defeq to) the product
topology and product uniformity, to be able to use freely continuity statements for the coordinate
functions, for instance.

## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is `lp`, the `L^p` norm on a product of (possibly
infinitely many) normed spaces, where the norm is
$$
\left(\sum ∥f (x)∥^p \right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, and some functions
have infinite `L^p` norm. These subtleties are not present in the case of finitely many metric
spaces, hence it is worth devoting a file to this specific case which is particularly well behaved.

Another related construction is `measure_theory.Lp`, the `L^p` norm on the space of functions from
a measure space to a normed space, where the norm is
$$
\left(\int ∥f (x)∥^p dμ\right)^{1/p}.
$$
This has all the same subtleties as `lp`, and the further subtlety that this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm).
The construction `pi_Lp` corresponds to the special case of `measure_theory.Lp` in which the basis
is a finite space equipped with the counting measure.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.

We also set up the theory for `pseudo_emetric_space` and `pseudo_metric_space`.
-/


open Real Set Filter IsROrC

open BigOperators uniformity TopologicalSpace Nnreal Ennreal

noncomputable section

variable {ι : Type _}

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances. -/
@[nolint unused_arguments]
def PiLp {ι : Type _} (p : ℝ) (α : ι → Type _) : Type _ :=
  ∀ i : ι, α i

instance {ι : Type _} (p : ℝ) (α : ι → Type _) [∀ i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨fun i => default⟩

instance fact_one_le_one_real : Fact ((1 : ℝ) ≤ 1) :=
  ⟨rfl.le⟩

instance fact_one_le_two_real : Fact ((1 : ℝ) ≤ 2) :=
  ⟨one_le_two⟩

namespace PiLp

variable (p : ℝ) [fact_one_le_p : Fact (1 ≤ p)] (α : ι → Type _) (β : ι → Type _)

/-- Canonical bijection between `pi_Lp p α` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
protected def equiv : PiLp p α ≃ ∀ i : ι, α i :=
  Equivₓ.refl _

@[simp]
theorem equiv_apply (x : PiLp p α) (i : ι) : PiLp.equiv p α x i = x i :=
  rfl

@[simp]
theorem equiv_symm_apply (x : ∀ i, α i) (i : ι) : (PiLp.equiv p α).symm x i = x i :=
  rfl

section

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `pi_Lp p α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/


variable [∀ i, EmetricSpace (α i)] [∀ i, PseudoEmetricSpace (β i)] [Fintype ι]

include fact_one_le_p

/-- Endowing the space `pi_Lp p β` with the `L^p` pseudoedistance. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `pseudo_emetric_space.replace_uniformity`. -/
def pseudoEmetricAux : PseudoEmetricSpace (PiLp p β) :=
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out
  { edist := fun f g => (∑ i, edist (f i) (g i) ^ p) ^ (1 / p),
    edist_self := fun f => by
      simp [edist, Ennreal.zero_rpow_of_pos Pos, Ennreal.zero_rpow_of_pos (inv_pos.2 Pos)],
    edist_comm := fun f g => by
      simp [edist, edist_comm],
    edist_triangle := fun f g h =>
      calc
        (∑ i, edist (f i) (h i) ^ p) ^ (1 / p) ≤ (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p) ^ (1 / p) := by
          apply Ennreal.rpow_le_rpow _ (one_div_nonneg.2 <| le_of_ltₓ Pos)
          refine' Finset.sum_le_sum fun i hi => _
          exact Ennreal.rpow_le_rpow (edist_triangle _ _ _) (le_transₓ zero_le_one fact_one_le_p.out)
        _ ≤ (∑ i, edist (f i) (g i) ^ p) ^ (1 / p) + (∑ i, edist (g i) (h i) ^ p) ^ (1 / p) :=
          Ennreal.Lp_add_le _ _ _ fact_one_le_p.out
         }

/-- Endowing the space `pi_Lp p α` with the `L^p` edistance. This definition is not satisfactory,
as it does not register the fact that the topology and the uniform structure coincide with the
product one. Therefore, we do not register it as an instance. Using this as a temporary emetric
space instance, we will show that the uniform structure is equal (but not defeq) to the product
one, and then register an instance in which we replace the uniform structure by the product one
using this emetric space and `emetric_space.replace_uniformity`. -/
def emetricAux : EmetricSpace (PiLp p α) :=
  { pseudoEmetricAux p α with
    eq_of_edist_eq_zero := fun f g hfg => by
      have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out
      let h := pseudo_emetric_aux p α
      have h : edist f g = (∑ i, edist (f i) (g i) ^ p) ^ (1 / p) := rfl
      simp [h, Ennreal.rpow_eq_zero_iff, Pos, asymm Pos, Finset.sum_eq_zero_iff_of_nonneg] at hfg
      exact funext hfg }

attribute [local instance] PiLp.emetricAux PiLp.pseudoEmetricAux

theorem lipschitz_with_equiv : LipschitzWith 1 (PiLp.equiv p β) := by
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out
  have cancel : p * (1 / p) = 1 := mul_div_cancel' 1 (ne_of_gtₓ Pos)
  intro x y
  simp only [edist, forall_prop_of_true, one_mulₓ, Finset.mem_univ, Finset.sup_le_iff, Ennreal.coe_one]
  intro i
  calc edist (x i) (y i) = (edist (x i) (y i) ^ p) ^ (1 / p) := by
      simp [← Ennreal.rpow_mul, cancel, -one_div]_ ≤ (∑ i, edist (x i) (y i) ^ p) ^ (1 / p) := by
      apply Ennreal.rpow_le_rpow _ (one_div_nonneg.2 <| le_of_ltₓ Pos)
      exact Finset.single_le_sum (fun i hi => (bot_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ i)

theorem antilipschitz_with_equiv : AntilipschitzWith ((Fintype.card ι : ℝ≥0 ) ^ (1 / p)) (PiLp.equiv p β) := by
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out
  have nonneg : 0 ≤ 1 / p := one_div_nonneg.2 (le_of_ltₓ Pos)
  have cancel : p * (1 / p) = 1 := mul_div_cancel' 1 (ne_of_gtₓ Pos)
  intro x y
  simp [edist, -one_div]
  calc (∑ i, edist (x i) (y i) ^ p) ^ (1 / p) ≤ (∑ i, edist (PiLp.equiv p β x) (PiLp.equiv p β y) ^ p) ^ (1 / p) := by
      apply Ennreal.rpow_le_rpow _ nonneg
      apply Finset.sum_le_sum fun i hi => _
      apply Ennreal.rpow_le_rpow _ (le_of_ltₓ Pos)
      exact
        Finset.le_sup
          (Finset.mem_univ
            i)_ = ((Fintype.card ι : ℝ≥0 ) ^ (1 / p) : ℝ≥0 ) * edist (PiLp.equiv p β x) (PiLp.equiv p β y) :=
      by
      simp only [nsmul_eq_mul, Finset.card_univ, Ennreal.rpow_one, Finset.sum_const,
        Ennreal.mul_rpow_of_nonneg _ _ nonneg, ← Ennreal.rpow_mul, cancel]
      have : (Fintype.card ι : ℝ≥0∞) = (Fintype.card ι : ℝ≥0 ) := (Ennreal.coe_nat (Fintype.card ι)).symm
      rw [this, Ennreal.coe_rpow_of_nonneg _ nonneg]

theorem aux_uniformity_eq : 𝓤 (PiLp p β) = @uniformity _ (Pi.uniformSpace _) := by
  have A : UniformInducing (PiLp.equiv p β) :=
    (antilipschitz_with_equiv p β).UniformInducing (lipschitz_with_equiv p β).UniformContinuous
  have : (fun x : PiLp p β × PiLp p β => ((PiLp.equiv p β) x.fst, (PiLp.equiv p β) x.snd)) = id := by
    ext i <;> rfl
  rw [← A.comap_uniformity, this, comap_id]

end

/-! ### Instances on finite `L^p` products -/


instance uniformSpace [∀ i, UniformSpace (β i)] : UniformSpace (PiLp p β) :=
  Pi.uniformSpace _

variable [Fintype ι]

include fact_one_le_p

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoEmetricSpace (β i)] : PseudoEmetricSpace (PiLp p β) :=
  (pseudoEmetricAux p β).replaceUniformity (aux_uniformity_eq p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [∀ i, EmetricSpace (α i)] : EmetricSpace (PiLp p α) :=
  (emetricAux p α).replaceUniformity (aux_uniformity_eq p α).symm

omit fact_one_le_p

theorem edist_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, PseudoEmetricSpace (β i)] (x y : PiLp p β) :
    edist x y = (∑ i, edist (x i) (y i) ^ p) ^ (1 / p) :=
  rfl

include fact_one_le_p

/-- pseudometric space instance on the product of finitely many psuedometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β) := by
  /- we construct the instance from the pseudo emetric space instance to avoid checking again that
    the uniformity is the same as the product uniformity, but we register nevertheless a nice formula
    for the distance -/
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out
  refine'
    PseudoEmetricSpace.toPseudoMetricSpaceOfDist (fun f g => (∑ i, dist (f i) (g i) ^ p) ^ (1 / p)) (fun f g => _)
      fun f g => _
  · simp [PiLp.edist_eq, Ennreal.rpow_eq_top_iff, asymm Pos, Pos, Ennreal.sum_eq_top_iff, edist_ne_top]
    
  · have A : ∀ i : ι, i ∈ (Finset.univ : Finset ι) → edist (f i) (g i) ^ p ≠ ⊤ := fun i hi => by
      simp [lt_top_iff_ne_top, edist_ne_top, le_of_ltₓ Pos]
    simp [dist, -one_div, PiLp.edist_eq, ← Ennreal.to_real_rpow, Ennreal.to_real_sum A, dist_edist]
    

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [∀ i, MetricSpace (α i)] : MetricSpace (PiLp p α) := by
  /- we construct the instance from the emetric space instance to avoid checking again that the
    uniformity is the same as the product uniformity, but we register nevertheless a nice formula
    for the distance -/
  have pos : 0 < p := lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out
  refine'
    EmetricSpace.toMetricSpaceOfDist (fun f g => (∑ i, dist (f i) (g i) ^ p) ^ (1 / p)) (fun f g => _) fun f g => _
  · simp [PiLp.edist_eq, Ennreal.rpow_eq_top_iff, asymm Pos, Pos, Ennreal.sum_eq_top_iff, edist_ne_top]
    
  · have A : ∀ i : ι, i ∈ (Finset.univ : Finset ι) → edist (f i) (g i) ^ p ≠ ⊤ := fun i hi => by
      simp [edist_ne_top, pos.le]
    simp [dist, -one_div, PiLp.edist_eq, ← Ennreal.to_real_rpow, Ennreal.to_real_sum A, dist_edist]
    

omit fact_one_le_p

theorem dist_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) :
    dist x y = (∑ i : ι, dist (x i) (y i) ^ p) ^ (1 / p) :=
  rfl

theorem nndist_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) :
    nndist x y = (∑ i : ι, nndist (x i) (y i) ^ p) ^ (1 / p) :=
  Subtype.ext <| by
    push_cast
    exact dist_eq _ _

include fact_one_le_p

/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
instance semiNormedGroup [∀ i, SemiNormedGroup (β i)] : SemiNormedGroup (PiLp p β) :=
  { Pi.addCommGroup with norm := fun f => (∑ i, ∥f i∥ ^ p) ^ (1 / p),
    dist_eq := fun x y => by
      simp [PiLp.dist_eq, dist_eq_norm, sub_eq_add_neg] }

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
instance normedGroup [∀ i, NormedGroup (α i)] : NormedGroup (PiLp p α) :=
  { PiLp.semiNormedGroup p α with }

omit fact_one_le_p

theorem norm_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (f : PiLp p β) :
    ∥f∥ = (∑ i, ∥f i∥ ^ p) ^ (1 / p) :=
  rfl

theorem nnnorm_eq {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (f : PiLp p β) :
    ∥f∥₊ = (∑ i, ∥f i∥₊ ^ p) ^ (1 / p) := by
  ext
  simp [Nnreal.coe_sum, norm_eq]

theorem norm_eq_of_nat {p : ℝ} [Fact (1 ≤ p)] {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (n : ℕ) (h : p = n)
    (f : PiLp p β) : ∥f∥ = (∑ i, ∥f i∥ ^ n) ^ (1 / (n : ℝ)) := by
  simp [norm_eq, h, Real.sqrt_eq_rpow, ← Real.rpow_nat_cast]

theorem norm_eq_of_L2 {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (x : PiLp 2 β) : ∥x∥ = sqrt (∑ i : ι, ∥x i∥ ^ 2) :=
  by
  rw [norm_eq_of_nat 2] <;> simp [sqrt_eq_rpow]

theorem nnnorm_eq_of_L2 {β : ι → Type _} [∀ i, SemiNormedGroup (β i)] (x : PiLp 2 β) :
    ∥x∥₊ = Nnreal.sqrt (∑ i : ι, ∥x i∥₊ ^ 2) :=
  Subtype.ext <| by
    push_cast
    exact norm_eq_of_L2 x

include fact_one_le_p

variable (𝕜 : Type _) [NormedField 𝕜]

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
instance normedSpace [∀ i, SemiNormedGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)] : NormedSpace 𝕜 (PiLp p β) :=
  { Pi.module ι β 𝕜 with
    norm_smul_le := by
      intro c f
      have : p * (1 / p) = 1 := mul_div_cancel' 1 (lt_of_lt_of_leₓ zero_lt_one fact_one_le_p.out).ne'
      simp only [PiLp.norm_eq, norm_smul, mul_rpow, norm_nonneg, ← Finset.mul_sum, Pi.smul_apply]
      rw [mul_rpow (rpow_nonneg_of_nonneg (norm_nonneg _) _), ← rpow_mul (norm_nonneg _), this, rpow_one]
      exact Finset.sum_nonneg fun i hi => rpow_nonneg_of_nonneg (norm_nonneg _) _ }

/- Register simplification lemmas for the applications of `pi_Lp` elements, as the usual lemmas
for Pi types will not trigger. -/
variable {𝕜 p α} [∀ i, SemiNormedGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)] (c : 𝕜)

variable (x y : PiLp p β) (x' y' : ∀ i, β i) (i : ι)

@[simp]
theorem zero_apply : (0 : PiLp p β) i = 0 :=
  rfl

@[simp]
theorem add_apply : (x + y) i = x i + y i :=
  rfl

@[simp]
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
theorem smul_apply : (c • x) i = c • x i :=
  rfl

@[simp]
theorem neg_apply : (-x) i = -x i :=
  rfl

@[simp]
theorem equiv_zero : PiLp.equiv p β 0 = 0 :=
  rfl

@[simp]
theorem equiv_symm_zero : (PiLp.equiv p β).symm 0 = 0 :=
  rfl

@[simp]
theorem equiv_add : PiLp.equiv p β (x + y) = PiLp.equiv p β x + PiLp.equiv p β y :=
  rfl

@[simp]
theorem equiv_symm_add : (PiLp.equiv p β).symm (x' + y') = (PiLp.equiv p β).symm x' + (PiLp.equiv p β).symm y' :=
  rfl

@[simp]
theorem equiv_sub : PiLp.equiv p β (x - y) = PiLp.equiv p β x - PiLp.equiv p β y :=
  rfl

@[simp]
theorem equiv_symm_sub : (PiLp.equiv p β).symm (x' - y') = (PiLp.equiv p β).symm x' - (PiLp.equiv p β).symm y' :=
  rfl

@[simp]
theorem equiv_neg : PiLp.equiv p β (-x) = -PiLp.equiv p β x :=
  rfl

@[simp]
theorem equiv_symm_neg : (PiLp.equiv p β).symm (-x') = -(PiLp.equiv p β).symm x' :=
  rfl

@[simp]
theorem equiv_smul : PiLp.equiv p β (c • x) = c • PiLp.equiv p β x :=
  rfl

@[simp]
theorem equiv_symm_smul : (PiLp.equiv p β).symm (c • x') = c • (PiLp.equiv p β).symm x' :=
  rfl

theorem nnnorm_equiv_symm_const {β} [SemiNormedGroup β] (b : β) :
    ∥(PiLp.equiv p fun _ : ι => β).symm (Function.const _ b)∥₊ = Fintype.card ι ^ (1 / p) * ∥b∥₊ := by
  have : p ≠ 0 := (zero_lt_one.trans_le (Fact.out <| 1 ≤ p)).ne'
  simp_rw [PiLp.nnnorm_eq, equiv_symm_apply, Function.const_applyₓ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nnreal.mul_rpow, ← Nnreal.rpow_mul, mul_one_div_cancel this, Nnreal.rpow_one]

theorem norm_equiv_symm_const {β} [SemiNormedGroup β] (b : β) :
    ∥(PiLp.equiv p fun _ : ι => β).symm (Function.const _ b)∥ = Fintype.card ι ^ (1 / p) * ∥b∥ :=
  (congr_argₓ coe <| nnnorm_equiv_symm_const b).trans <| by
    simp

theorem nnnorm_equiv_symm_one {β} [SemiNormedGroup β] [One β] :
    ∥(PiLp.equiv p fun _ : ι => β).symm 1∥₊ = Fintype.card ι ^ (1 / p) * ∥(1 : β)∥₊ :=
  (nnnorm_equiv_symm_const (1 : β)).trans rfl

theorem norm_equiv_symm_one {β} [SemiNormedGroup β] [One β] :
    ∥(PiLp.equiv p fun _ : ι => β).symm 1∥ = Fintype.card ι ^ (1 / p) * ∥(1 : β)∥ :=
  (norm_equiv_symm_const (1 : β)).trans rfl

end PiLp

