import OAI.Analysis.PDE.Green.Cutoff

/-! Dominated-convergence statements for the defining-function cutoffs. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {S : Set E}

theorem integral_boundaryCutoff_tendsto {r f : E → ℝ}
    (hr : Continuous r) (hf : Continuous f) (hfi : IntegrableOn f S μ)
    (hneg : ∀ x ∈ S, r x < 0) (hS : MeasurableSet S) :
    Tendsto (fun k : ℕ ↦ ∫ x in S, boundaryCutoff (r x) k * f x ∂μ)
      atTop (𝓝 (∫ x in S, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
  · intro k
    exact ((Real.smoothTransition.continuous.comp (continuous_const.mul hr)).mul hf).aestronglyMeasurable
  · exact hfi.norm
  · intro k
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul]
    have hc : ‖boundaryCutoff (r x) k‖ ≤ 1 := by
      unfold boundaryCutoff
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (f x))
  · filter_upwards [ae_restrict_mem hS] with x hx
    simpa only [one_mul] using (boundaryCutoff_tendsto (hneg x hx)).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ f x) atTop (𝓝 (f x)))

theorem integral_transitionSlope_tendsto_zero {r b : E → ℝ}
    (hr : Continuous r) (hbi : IntegrableOn b S μ) :
    Tendsto (fun k : ℕ ↦ ∫ x in S, transitionSlope (-((k : ℝ) + 1) * r x) * b x ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨C,hC0,hC⟩ := exists_transitionSlope_bound
  have h := tendsto_integral_of_dominated_convergence (μ := μ.restrict S)
    (F := fun k x ↦ transitionSlope (-((k : ℝ) + 1) * r x) * b x)
    (f := fun _ ↦ (0 : ℝ)) (fun x ↦ C * ‖b x‖) ?_ ?_ ?_ ?_
  · simpa only [integral_zero] using h
  · intro k
    exact (continuous_transitionSlope.comp (continuous_const.mul hr)).aestronglyMeasurable.mul
      hbi.aestronglyMeasurable
  · exact hbi.norm.const_mul C
  · intro k
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg (b x))
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [zero_mul] using (transitionSlope_cutoff_tendsto (r x)).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ b x) atTop (𝓝 (b x)))

end OAI.Analysis.PDE.Green
