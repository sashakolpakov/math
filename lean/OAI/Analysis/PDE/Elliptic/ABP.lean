import OAI.Analysis.PDE.Elliptic.TraceCoercivity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Alexandrov–Bakelman–Pucci contact estimate, with the Laplacian
controlling the Hessian determinant only on the lower contact set. -/
theorem contact_ball_measure_le_laplacian_pow
    (μ : Measure E) [IsAddHaarMeasure μ] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R) :
    μ (Metric.ball (0 : E) (-f x₀ / R)) ≤
      ∫⁻ x in lowerContactSet K f,
        ENNReal.ofReal (Laplacian.laplacian f x ^ Module.finrank ℝ E) ∂μ := by
  refine (contact_ball_measure_le_hessian_determinant μ hK hf hx₀ hnegative
    hboundary hR hradius).trans ?_
  exact setLIntegral_mono' (measurableSet_lowerContactSet hf) fun x hx ↦
    ENNReal.ofReal_le_ofReal (abs_det_fderiv_gradient_le_laplacian_pow hf hx)

/-- Power form of the ABP bound. This form avoids taking a dimension-th
root and also applies in the zero-dimensional case. -/
theorem abp_laplacian_power_bound
    (μ : Measure E) [IsAddHaarMeasure μ] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R) :
    ENNReal.ofReal (-f x₀ / R) ^ Module.finrank ℝ E * μ (Metric.ball (0 : E) 1) ≤
      ∫⁻ x in lowerContactSet K f,
        ENNReal.ofReal (Laplacian.laplacian f x ^ Module.finrank ℝ E) ∂μ := by
  have h := contact_ball_measure_le_laplacian_pow μ hK hf hx₀ hnegative hboundary hR hradius
  rwa [addHaar_ball_of_pos μ 0 (div_pos (neg_pos.mpr hnegative) hR),
    ENNReal.ofReal_pow (div_pos (neg_pos.mpr hnegative) hR).le] at h

/-- ABP for an actual, possibly variable-coefficient uniformly elliptic
operator. Only its pointwise ellipticity and the differential inequality
on the contact set enter the estimate. -/
theorem abp_ellipticTrace_bound
    (μ : Measure E) [IsAddHaarMeasure μ] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R)
    (A : E → E →L[ℝ] E) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ x ∈ lowerContactSet K f, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (g : E → ℝ) (hg : ∀ x ∈ lowerContactSet K f, ellipticTrace A f x ≤ g x) :
    μ (Metric.ball (0 : E) (-f x₀ / R)) ≤
      ∫⁻ x in lowerContactSet K f,
        ENNReal.ofReal ((max (g x) 0 / lam) ^ Module.finrank ℝ E) ∂μ := by
  refine (contact_ball_measure_le_laplacian_pow μ hK hf hx₀ hnegative
    hboundary hR hradius).trans ?_
  apply setLIntegral_mono' (measurableSet_lowerContactSet hf)
  intro x hx
  apply ENNReal.ofReal_le_ofReal
  have hnonneg : 0 ≤ Laplacian.laplacian f x := by
    have h := (fderiv_gradient_isPositive_of_contact hf hx).trace_nonneg
    rwa [trace_fderiv_gradient hf] at h
  have hupper : Laplacian.laplacian f x ≤ max (g x) 0 / lam :=
    (laplacian_le_ellipticTrace_div_of_contact hf A hx hlam (hA x hx)).trans
      (div_le_div_of_nonneg_right ((hg x hx).trans (le_max_left _ _)) hlam.le)
  exact pow_le_pow_left₀ hnonneg hupper _

theorem abp_ellipticTrace_power_bound
    (μ : Measure E) [IsAddHaarMeasure μ] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R)
    (A : E → E →L[ℝ] E) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ x ∈ lowerContactSet K f, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (g : E → ℝ) (hg : ∀ x ∈ lowerContactSet K f, ellipticTrace A f x ≤ g x) :
    ENNReal.ofReal (-f x₀ / R) ^ Module.finrank ℝ E * μ (Metric.ball (0 : E) 1) ≤
      ∫⁻ x in lowerContactSet K f,
        ENNReal.ofReal ((max (g x) 0 / lam) ^ Module.finrank ℝ E) ∂μ := by
  have h := abp_ellipticTrace_bound μ hK hf hx₀ hnegative hboundary hR hradius A hlam hA g hg
  rwa [addHaar_ball_of_pos μ 0 (div_pos (neg_pos.mpr hnegative) hR),
    ENNReal.ofReal_pow (div_pos (neg_pos.mpr hnegative) hR).le] at h

end OAI.Analysis.PDE.Elliptic
