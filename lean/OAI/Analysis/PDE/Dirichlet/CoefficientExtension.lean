import OAI.Analysis.PDE.Dirichlet.L2Coefficient

open Set _root_.MeasureTheory Filter
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}

/-- Extend a coefficient field by the identity outside the physical domain.
This gives coercivity on the whole integration cell without requiring the
original coefficient to remain elliptic beyond the domain. -/
def identityExtendCoefficient (Ω : Set X) (A : X → E →L[ℝ] E) : X → E →L[ℝ] E := by
  classical
  exact Ω.piecewise A (fun _ ↦ ContinuousLinearMap.id ℝ E)

omit [MeasurableSpace X] in
@[simp] theorem identityExtendCoefficient_of_mem (Ω : Set X) (A : X → E →L[ℝ] E)
    {x : X} (hx : x ∈ Ω) : identityExtendCoefficient Ω A x = A x := by
  classical
  simp [identityExtendCoefficient, hx]

omit [MeasurableSpace X] in
@[simp] theorem identityExtendCoefficient_of_not_mem (Ω : Set X) (A : X → E →L[ℝ] E)
    {x : X} (hx : x ∉ Ω) :
    identityExtendCoefficient Ω A x = ContinuousLinearMap.id ℝ E := by
  classical
  simp [identityExtendCoefficient, hx]

theorem identityExtendCoefficient_measurable (Ω : Set X) (hΩ : MeasurableSet Ω)
    (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A (μ.restrict Ω)) :
    AEStronglyMeasurable (identityExtendCoefficient Ω A) μ := by
  classical
  exact hA.piecewise hΩ aestronglyMeasurable_const

theorem identityExtendCoefficient_bound (Ω : Set X) (A : X → E →L[ℝ] E)
    {M : ℝ} (hAM : ∀ᵐ x ∂μ, x ∈ Ω → ‖A x‖ ≤ M) :
    ∀ᵐ x ∂μ, ‖identityExtendCoefficient Ω A x‖ ≤ max M 1 := by
  filter_upwards [hAM] with x hx
  by_cases hmem : x ∈ Ω
  · rw [identityExtendCoefficient_of_mem Ω A hmem]
    exact (hx hmem).trans (le_max_left _ _)
  · rw [identityExtendCoefficient_of_not_mem Ω A hmem]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_right _ _)

theorem identityExtendCoefficient_elliptic (Ω : Set X) (A : X → E →L[ℝ] E)
    {lam : ℝ} (hell : ∀ᵐ x ∂μ, x ∈ Ω → ∀ v : E,
      lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) :
    ∀ᵐ x ∂μ, ∀ v : E,
      min lam 1 * ‖v‖ ^ 2 ≤ inner ℝ v (identityExtendCoefficient Ω A x v) := by
  filter_upwards [hell] with x hx
  intro v
  by_cases hmem : x ∈ Ω
  · rw [identityExtendCoefficient_of_mem Ω A hmem]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (hx hmem v)
  · rw [identityExtendCoefficient_of_not_mem Ω A hmem]
    simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, one_mul] using
      mul_le_mul_of_nonneg_right (min_le_right lam 1) (sq_nonneg ‖v‖)

end OAI.Analysis.PDE.Dirichlet
