import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftTaylor

noncomputable section
open Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_of_real_holder_bound (f : E → F) {α C : ℝ} (hα : 0 < α)
    (hb : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change Tendsto f (𝓝 x) (𝓝 (f x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun y : E ↦ C * ‖y - x‖ ^ α) :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
      (fun _ ↦ Or.inr hα.le))
  have ht : Tendsto (fun y : E ↦ C * ‖y - x‖ ^ α) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto x
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun y ↦ hb y x) ht

end OAI.Analysis.PDE.Schauder
