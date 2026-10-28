import OAI.Analysis.PDE.Elliptic.Boundary.Correction

/-! Extraction of the actual mixed Hessian from the tangent-field estimate. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def chartMixedHessian (u : E → ℝ) (T F : E → E) (v z : E) : ℝ :=
  fderiv ℝ (fderiv ℝ u) (F z) (fderiv ℝ F z v) (T (F z))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem chartMixedHessian_eq {u : E → ℝ} {T F : E → E}
    (hu : ContDiff ℝ 2 u) (hT : Differentiable ℝ T) (v z : E) :
    chartMixedHessian u T F v z = chartFieldNormal u T F v z - fieldNormalCorrection u T F v z := by
  rw [chartFieldNormal_eq hu hT]
  dsimp only [chartMixedHessian, fieldNormalCorrection]
  ring

omit [Nontrivial E] in
theorem chart_mixed_holder_from_normal
    {u : E → ℝ} {T F : E → E} {v : E} {V α C : ℝ}
    (hu : ContDiff ℝ 2 u) (hT : ContDiff ℝ 2 T) (hv : ‖v‖ = 1) (hV : 0 ≤ V) (hα : α ≤ 1)
    (hF : ∀ z ∈ closedHalfBall v, ContDiffAt ℝ 2 F z)
    (hu1 : ∀ z ∈ closedHalfBall v, ‖fderiv ℝ u (F z)‖ ≤ V)
    (hu2 : ∀ z ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (F z)‖ ≤ V)
    (hT1 : ∀ z ∈ closedHalfBall v, ‖fderiv ℝ T (F z)‖ ≤ V)
    (hT2 : ∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 T (F z)‖ ≤ V)
    (hF1 : ∀ z ∈ closedHalfBall v, ‖fderiv ℝ F z‖ ≤ V)
    (hF2 : ∀ z ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 F z‖ ≤ V)
    (hnormal : ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
      |chartFieldNormal u T F v z - chartFieldNormal u T F v z'| ≤ C * ‖z - z'‖ ^ α) :
    ∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 → inner ℝ v z = 0 → inner ℝ v z' = 0 →
      |chartMixedHessian u T F v z - chartMixedHessian u T F v z'| ≤
        (C + V ^ 3 + 2 * V ^ 4) * ‖z - z'‖ ^ α := by
  intro z z' hz hz' hp hp'
  have hzmem : z ∈ closedHalfBall v := ⟨by linarith, by simp [hp]⟩
  have hzmem' : z' ∈ closedHalfBall v := ⟨by linarith, by simp [hp']⟩
  have hc := fieldNormalCorrection_lipschitz hu hT (convex_closedHalfBall v) hF hV
    hv.le hu1 hu2 hT1 hT2 hF1 hF2 hzmem hzmem'
  have hn := hnormal z z' hz hz' hp hp'
  have hd : ‖z - z'‖ ≤ ‖z - z'‖ ^ α := Real.self_le_rpow_of_le_one
    (norm_nonneg _) ((norm_sub_le z z').trans (by linarith)) hα
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ V ^ 3 + 2 * V ^ 4 by positivity)
  rw [chartMixedHessian_eq hu (hT.differentiable (by norm_num)),
    chartMixedHessian_eq hu (hT.differentiable (by norm_num))]
  have he : (chartFieldNormal u T F v z - fieldNormalCorrection u T F v z) -
      (chartFieldNormal u T F v z' - fieldNormalCorrection u T F v z') =
      (chartFieldNormal u T F v z - chartFieldNormal u T F v z') -
      (fieldNormalCorrection u T F v z - fieldNormalCorrection u T F v z') := by ring
  rw [he]
  have ht := abs_sub_le (chartFieldNormal u T F v z - chartFieldNormal u T F v z') 0
    (fieldNormalCorrection u T F v z - fieldNormalCorrection u T F v z')
  simp only [sub_zero, zero_sub, abs_neg] at ht
  nlinarith

end OAI.Analysis.PDE.Elliptic
