import OAI.Analysis.PDE.Elliptic.ABP

open Set _root_.MeasureTheory _root_.MeasureTheory.Measure
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The negative portion of the lower contact set. Restricting to this
portion is important for the level-set growth argument. -/
def negativeContactSet (K : Set E) (f : E → ℝ) : Set E :=
  lowerContactSet K f ∩ {x | f x < 0}

omit [FiniteDimensional ℝ E] in
theorem measurableSet_negativeContactSet {K : Set E} {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) : MeasurableSet (negativeContactSet K f) :=
  (measurableSet_lowerContactSet hf).inter (isOpen_lt hf.continuous continuous_const).measurableSet

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every small slope is already attained in the negative contact set. -/
theorem ball_subset_gradient_image_negativeContactSet {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : Differentiable ℝ f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R) :
    Metric.ball (0 : E) (-f x₀ / R) ⊆ gradient f '' negativeContactSet K f := by
  intro v hv
  obtain ⟨y, hy, heq⟩ := ball_subset_gradient_image_lowerContactSet hK hf hx₀ hnegative
    hboundary hR hradius hv
  refine ⟨y, ⟨hy, ?_⟩, heq⟩
  have hs := hy.2 x₀ hx₀
  have hnorm : ‖fderiv ℝ f y‖ = ‖v‖ := by
    rw [← toDual_gradient, heq, LinearIsometryEquiv.norm_map]
  have hsmall : ‖v‖ * R < -f x₀ := (lt_div_iff₀ hR).mp (by simpa using hv)
  have hl : fderiv ℝ f y (y - x₀) ≤ ‖v‖ * R := by
    calc
      _ ≤ ‖fderiv ℝ f y‖ * ‖y - x₀‖ := (le_abs_self _).trans ((fderiv ℝ f y).le_opNorm _)
      _ ≤ ‖v‖ * R := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left
          (hradius y (interior_subset hy.1)) (norm_nonneg v)
  rw [map_sub] at hs hl
  change f y < 0
  linarith

theorem negative_contact_measure_le_hessian_determinant
    (μ : Measure E) [IsAddHaarMeasure μ] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R) :
    μ (Metric.ball (0 : E) (-f x₀ / R)) ≤
      ∫⁻ x in negativeContactSet K f, ENNReal.ofReal |(fderiv ℝ (gradient f) x).det| ∂μ := by
  have hgrad : Differentiable ℝ (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.differentiable.comp
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
  exact (measure_mono (ball_subset_gradient_image_negativeContactSet hK
    (hf.differentiable (by norm_num)) hx₀ hnegative hboundary hR hradius)).trans
      (addHaar_image_le_lintegral_abs_det_fderiv μ (measurableSet_negativeContactSet hf)
        (fun x _ ↦ (hgrad x).hasFDerivAt.hasFDerivWithinAt))

/-- The ABP estimate with forcing integrated only over negative contacts.
This stronger localization converts the estimate into sublevel-set growth. -/
theorem abp_negative_contact_bound
    (μ : Measure E) [IsAddHaarMeasure μ] {K : Set E} (hK : IsCompact K)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x₀ : E} (hx₀ : x₀ ∈ K)
    (hnegative : f x₀ < 0) (hboundary : ∀ x ∈ K, x ∉ interior K → 0 ≤ f x)
    {R : ℝ} (hR : 0 < R) (hradius : ∀ x ∈ K, ‖x - x₀‖ ≤ R)
    (A : E → E →L[ℝ] E) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ x ∈ negativeContactSet K f, ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (g : E → ℝ) (hg : ∀ x ∈ negativeContactSet K f, ellipticTrace A f x ≤ g x) :
    μ (Metric.ball (0 : E) (-f x₀ / R)) ≤
      ∫⁻ x in negativeContactSet K f,
        ENNReal.ofReal ((max (g x) 0 / lam) ^ Module.finrank ℝ E) ∂μ := by
  refine (negative_contact_measure_le_hessian_determinant μ hK hf hx₀ hnegative
    hboundary hR hradius).trans ?_
  apply setLIntegral_mono' (measurableSet_negativeContactSet hf)
  intro x hx
  apply ENNReal.ofReal_le_ofReal
  refine (abs_det_fderiv_gradient_le_laplacian_pow hf hx.1).trans ?_
  have hnonneg : 0 ≤ Laplacian.laplacian f x := by
    have h := (fderiv_gradient_isPositive_of_contact hf hx.1).trace_nonneg
    rwa [trace_fderiv_gradient hf] at h
  have hupper : Laplacian.laplacian f x ≤ max (g x) 0 / lam :=
    (laplacian_le_ellipticTrace_div_of_contact hf A hx.1 hlam (hA x hx)).trans
      (div_le_div_of_nonneg_right ((hg x hx).trans (le_max_left _ _)) hlam.le)
  exact pow_le_pow_left₀ hnonneg hupper _

end OAI.Analysis.PDE.Elliptic
