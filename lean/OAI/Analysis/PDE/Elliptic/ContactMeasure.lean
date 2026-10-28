import OAI.Analysis.PDE.Elliptic.Contact
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.Jacobian

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem measurableSet_lowerContactSet {K : Set E} {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) : MeasurableSet (lowerContactSet K f) := by
  have hDf : Continuous (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous
  exact isOpen_interior.measurableSet.inter
    (isClosed_supporting_tangent_set hf.continuous hDf).measurableSet

omit [MeasurableSpace E] [BorelSpace E] in
/-- Riesz identification turns the slope coverage into coverage by the
actual gradient in the original Euclidean space. -/
theorem ball_subset_gradient_image_lowerContactSet {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : Differentiable ℝ f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R) :
    Metric.ball (0 : E) (-f x₀ / R) ⊆ gradient f '' lowerContactSet K f := by
  intro v hv
  have hl : InnerProductSpace.toDual ℝ E v ∈ Metric.ball 0 (-f x₀ / R) := by
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hv
  obtain ⟨y, hy, heq⟩ := ball_subset_fderiv_image_lowerContactSet hK hf hx₀ hnegative
    hboundary hR hradius hl
  refine ⟨y, hy, ?_⟩
  simp only [gradient, heq, LinearIsometryEquiv.symm_apply_apply]

/-- The ABP contact-measure inequality. The Jacobian is the actual
derivative of the gradient; injectivity of that gradient is not assumed. -/
theorem contact_ball_measure_le_hessian_determinant
    (μ : Measure E) [IsAddHaarMeasure μ] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R) :
    μ (Metric.ball (0 : E) (-f x₀ / R)) ≤
      ∫⁻ x in lowerContactSet K f, ENNReal.ofReal |(fderiv ℝ (gradient f) x).det| ∂μ := by
  have hgrad : Differentiable ℝ (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.differentiable.comp
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
  calc
    μ (Metric.ball (0 : E) (-f x₀ / R)) ≤ μ (gradient f '' lowerContactSet K f) :=
      measure_mono (ball_subset_gradient_image_lowerContactSet hK
        (hf.differentiable (by norm_num)) hx₀ hnegative hboundary hR hradius)
    _ ≤ _ := addHaar_image_le_lintegral_abs_det_fderiv μ (measurableSet_lowerContactSet hf)
      (fun x _ ↦ (hgrad x).hasFDerivAt.hasFDerivWithinAt)

end OAI.Analysis.PDE.Elliptic
