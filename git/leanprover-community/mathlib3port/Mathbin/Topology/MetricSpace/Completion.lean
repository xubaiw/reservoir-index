/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Topology.UniformSpace.Completion
import Mathbin.Topology.MetricSpace.Isometry
import Mathbin.Topology.Instances.Real

/-!
# The completion of a metric space

Completion of uniform spaces are already defined in `topology.uniform_space.completion`. We show
here that the uniform space completion of a metric space inherits a metric space structure,
by extending the distance to the completion and checking that it is indeed a distance, and that
it defines the same uniformity as the already defined uniform structure on the completion
-/


open Set Filter UniformSpace Metric

open Filter TopologicalSpace uniformity

noncomputable section

universe u v

variable {α : Type u} {β : Type v} [PseudoMetricSpace α]

namespace UniformSpace.Completion

/-- The distance on the completion is obtained by extending the distance on the original space,
by uniform continuity. -/
instance : HasDist (Completion α) :=
  ⟨Completion.extension₂ dist⟩

/-- The new distance is uniformly continuous. -/
protected theorem uniform_continuous_dist : UniformContinuous fun p : Completion α × Completion α => dist p.1 p.2 :=
  uniform_continuous_extension₂ dist

/-- The new distance is continuous. -/
protected theorem continuous_dist [TopologicalSpace β] {f g : β → Completion α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => dist (f x) (g x) :=
  Completion.uniform_continuous_dist.Continuous.comp (hf.prod_mk hg : _)

/-- The new distance is an extension of the original distance. -/
@[simp]
protected theorem dist_eq (x y : α) : dist (x : Completion α) y = dist x y :=
  Completion.extension₂_coe_coe uniform_continuous_dist _ _

/- Let us check that the new distance satisfies the axioms of a distance, by starting from the
properties on α and extending them to `completion α` by continuity. -/
protected theorem dist_self (x : Completion α) : dist x x = 0 := by
  apply induction_on x
  · refine' is_closed_eq _ continuous_const
    exact completion.continuous_dist continuous_id continuous_id
    
  · intro a
    rw [completion.dist_eq, dist_self]
    

protected theorem dist_comm (x y : Completion α) : dist x y = dist y x := by
  apply induction_on₂ x y
  · exact
      is_closed_eq (completion.continuous_dist continuous_fst continuous_snd)
        (completion.continuous_dist continuous_snd continuous_fst)
    
  · intro a b
    rw [completion.dist_eq, completion.dist_eq, dist_comm]
    

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
protected theorem dist_triangle (x y z : Completion α) : dist x z ≤ dist x y + dist y z := by
  apply induction_on₃ x y z
  · refine' is_closed_le _ (Continuous.add _ _) <;>
      apply_rules [completion.continuous_dist, Continuous.fst, Continuous.snd, continuous_id]
    
  · intro a b c
    rw [completion.dist_eq, completion.dist_eq, completion.dist_eq]
    exact dist_triangle a b c
    

/-- Elements of the uniformity (defined generally for completions) can be characterized in terms
of the distance. -/
protected theorem mem_uniformity_dist (s : Set (Completion α × Completion α)) :
    s ∈ 𝓤 (Completion α) ↔ ∃ ε > 0, ∀ {a b}, dist a b < ε → (a, b) ∈ s := by
  constructor
  · /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in `α` is an
        entourage, so it contains an `ε`-neighborhood of the diagonal by definition of the entourages
        in metric spaces. Then `t` contains an `ε`-neighborhood of the diagonal in `completion α`, as
        closed properties pass to the completion. -/
    intro hs
    rcases mem_uniformity_is_closed hs with ⟨t, ht, ⟨tclosed, ts⟩⟩
    have A : { x : α × α | (coe x.1, coe x.2) ∈ t } ∈ uniformity α :=
      uniform_continuous_def.1 (uniform_continuous_coe α) t ht
    rcases mem_uniformity_dist.1 A with ⟨ε, εpos, hε⟩
    refine' ⟨ε, εpos, fun x y hxy => _⟩
    have : ε ≤ dist x y ∨ (x, y) ∈ t := by
      apply induction_on₂ x y
      · have :
          { x : completion α × completion α | ε ≤ dist x.fst x.snd ∨ (x.fst, x.snd) ∈ t } =
            { p : completion α × completion α | ε ≤ dist p.1 p.2 } ∪ t :=
          by
          ext <;> simp
        rw [this]
        apply IsClosed.union _ tclosed
        exact is_closed_le continuous_const completion.uniform_continuous_dist.continuous
        
      · intro x y
        rw [completion.dist_eq]
        by_cases' h : ε ≤ dist x y
        · exact Or.inl h
          
        · have Z := hε (not_leₓ.1 h)
          simp only [Set.mem_set_of_eq] at Z
          exact Or.inr Z
          
        
    simp only [not_le.mpr hxy, false_orₓ, not_leₓ] at this
    exact ts this
    
  · /- Start from a set `s` containing an ε-neighborhood of the diagonal in `completion α`. To show
        that it is an entourage, we use the fact that `dist` is uniformly continuous on
        `completion α × completion α` (this is a general property of the extension of uniformly
        continuous functions). Therefore, the preimage of the ε-neighborhood of the diagonal in ℝ
        is an entourage in `completion α × completion α`. Massaging this property, it follows that
        the ε-neighborhood of the diagonal is an entourage in `completion α`, and therefore this is
        also the case of `s`. -/
    rintro ⟨ε, εpos, hε⟩
    let r : Set (ℝ × ℝ) := { p | dist p.1 p.2 < ε }
    have : r ∈ uniformity ℝ := Metric.dist_mem_uniformity εpos
    have T := uniform_continuous_def.1 (@completion.uniform_continuous_dist α _) r this
    simp only [uniformity_prod_eq_prod, mem_prod_iff, exists_prop, Filter.mem_map, Set.mem_set_of_eq] at T
    rcases T with ⟨t1, ht1, t2, ht2, ht⟩
    refine' mem_of_superset ht1 _
    have A : ∀ a b : completion α, (a, b) ∈ t1 → dist a b < ε := by
      intro a b hab
      have : ((a, b), (a, a)) ∈ t1 ×ˢ t2 := ⟨hab, refl_mem_uniformity ht2⟩
      have I := ht this
      simp [completion.dist_self, Real.dist_eq, completion.dist_comm] at I
      exact lt_of_le_of_ltₓ (le_abs_self _) I
    show t1 ⊆ s
    · rintro ⟨a, b⟩ hp
      have : dist a b < ε := A a b hp
      exact hε this
      
    

/-- If two points are at distance 0, then they coincide. -/
protected theorem eq_of_dist_eq_zero (x y : Completion α) (h : dist x y = 0) : x = y := by
  /- This follows from the separation of `completion α` and from the description of
    entourages in terms of the distance. -/
  have : SeparatedSpace (completion α) := by
    infer_instance
  refine' separated_def.1 this x y fun s hs => _
  rcases(completion.mem_uniformity_dist s).1 hs with ⟨ε, εpos, hε⟩
  rw [← h] at εpos
  exact hε εpos

/-- Reformulate `completion.mem_uniformity_dist` in terms that are suitable for the definition
of the metric space structure. -/
protected theorem uniformity_dist' : 𝓤 (Completion α) = ⨅ ε : { ε : ℝ // 0 < ε }, 𝓟 { p | dist p.1 p.2 < ε.val } := by
  ext s
  rw [mem_infi_of_directed]
  · simp [completion.mem_uniformity_dist, subset_def]
    
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    use ⟨min r p, lt_minₓ hr hp⟩
    simp (config := { contextual := true })[lt_min_iff, (· ≥ ·)]
    

protected theorem uniformity_dist : 𝓤 (Completion α) = ⨅ ε > 0, 𝓟 { p | dist p.1 p.2 < ε } := by
  simpa [infi_subtype] using @completion.uniformity_dist' α _

/-- Metric space structure on the completion of a pseudo_metric space. -/
instance : MetricSpace (Completion α) where
  dist_self := Completion.dist_self
  eq_of_dist_eq_zero := Completion.eq_of_dist_eq_zero
  dist_comm := Completion.dist_comm
  dist_triangle := Completion.dist_triangle
  dist := dist
  toUniformSpace := by
    infer_instance
  uniformity_dist := Completion.uniformity_dist

/-- The embedding of a metric space in its completion is an isometry. -/
theorem coe_isometry : Isometry (coe : α → Completion α) :=
  Isometry.of_dist_eq Completion.dist_eq

@[simp]
protected theorem edist_eq (x y : α) : edist (x : Completion α) y = edist x y :=
  coe_isometry x y

end UniformSpace.Completion

