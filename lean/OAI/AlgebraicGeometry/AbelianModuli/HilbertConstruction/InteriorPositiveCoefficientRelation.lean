import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConvexPositiveFunctionalInterior
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-! # Interior Positive Coefficient Relation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InteriorPositiveCoefficientRelation

noncomputable section

/-! An interior point gives a relation with every coefficient strictly
positive, including generators not needed in a particular convex combination. -/
open scoped BigOperators Classical _root_.Topology
universe u v
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E]
variable {ι : Type v} [Fintype ι]

omit [IsTopologicalAddGroup E] in
theorem exists_positive_coefficients_sum_zero_of_interior (v : ι → E)
    (hzero : (0 : E) ∈ interior (convexHull ℝ (Set.range v))) :
    ∃ c : ι → ℝ, (∀ i, 0 < c i) ∧ ∑ i, c i • v i = 0 := by
  let z := ∑ i, v i
  have hcont : Continuous (fun t : ℝ => -t • z) := continuous_neg.smul continuous_const
  have hU : {t : ℝ | -t • z ∈ convexHull ℝ (Set.range v)} ∈ 𝓝 (0 : ℝ) := by
    have hnb := mem_interior_iff_mem_nhds.mp hzero
    have hn : convexHull ℝ (Set.range v) ∈ 𝓝 (- (0 : ℝ) • z) := by simpa using hnb
    exact hcont.continuousAt.preimage_mem_nhds hn
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hh : 0 < ε / 2 := by linarith
  have hc : -(ε / 2) • z ∈ convexHull ℝ (Set.range v) := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hh]
    linarith)
  rw [convexHull_range_eq_exists_affineCombination] at hc
  obtain ⟨s, a, ha, hsum, hc⟩ := hc
  rw [Finset.affineCombination_eq_linear_combination s v a hsum] at hc
  refine ⟨fun i => (if i ∈ s then a i else 0) + ε / 2, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · simp only [hi, ite_true]
      exact add_pos_of_nonneg_of_pos (ha i hi) hh
    · simpa only [hi, ite_false, zero_add] using hh
  · simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
    rw [Finset.sum_ite, ← Finset.smul_sum]
    rw [Finset.filter_mem_eq_of_subset (Finset.subset_univ s)]
    simp only [Finset.sum_const_zero, add_zero]
    rw [hc]
    rw [neg_smul]
    exact neg_add_cancel ((ε / 2) • z)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InteriorPositiveCoefficientRelation
