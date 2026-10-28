import OAI.Analysis.Calculus.Coefficients.Global

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Derivatives commute with positive mollification without any support or
global boundedness assumption on the input. Compactness is used only on the
local translated support of the mollifier. -/
theorem hasFDerivAt_smoothField
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : ContDiff ℝ 1 f)
    (x₀ : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (smoothField φ f) (smoothField φ (fderiv ℝ f) x₀) x₀ := by
  have hDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨C,hC⟩ := (isCompact_closedBall x₀ (φ.rOut+1)).exists_bound_of_continuousOn hDf.continuousOn
  change HasFDerivAt (fun x ↦ ∫ y, φ.normed volume y • f (x-y))
    (∫ y, φ.normed volume y • fderiv ℝ f (x₀-y)) x₀
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds x₀ zero_lt_one)
  · exact Eventually.of_forall fun x ↦
      (φ.continuous_normed.smul (hf.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · exact integrable_smoothField φ f hf.continuous x₀
  · exact (φ.continuous_normed.smul (hDf.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro y x hx
    change ‖φ.normed volume y • fderiv ℝ f (x-y)‖ ≤ φ.normed volume y*C
    by_cases hy : φ.normed volume y = 0
    · simp [hy]
    · have hyball : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin m)) φ.rOut := by
        rw [←φ.support_normed_eq (μ := volume)]
        exact hy
      have hyNorm : ‖y‖ < φ.rOut := by simpa only [Metric.mem_ball,dist_zero_right] using hyball
      have hxDist : dist x x₀ < 1 := hx
      have hxy : x-y ∈ Metric.closedBall x₀ (φ.rOut+1) := by
        rw [Metric.mem_closedBall,dist_eq_norm]
        calc
          ‖x-y-x₀‖ = ‖(x-x₀)-y‖ := by congr 1; abel
          _ ≤ ‖x-x₀‖+‖y‖ := norm_sub_le _ _
          _ ≤ φ.rOut+1 := by rw [←dist_eq_norm]; linarith
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hC (x-y) hxy) (φ.nonneg_normed y)
  · exact φ.integrable_normed.mul_const C
  · apply Eventually.of_forall
    intro y x _
    have hd : HasFDerivAt (fun x ↦ f (x-y)) (fderiv ℝ f (x-y)) x := by
      simpa using! (hf.differentiable one_ne_zero (x-y)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const y)
    exact hd.const_smul (φ.normed volume y)

omit [CompleteSpace F] in
theorem fderiv_smoothField
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : ContDiff ℝ 1 f) :
    fderiv ℝ (smoothField φ f) = smoothField φ (fderiv ℝ f) := by
  funext x
  exact (hasFDerivAt_smoothField φ f hf x).fderiv

omit [CompleteSpace F] in
theorem second_fderiv_smoothField
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : ContDiff ℝ 2 f) :
    fderiv ℝ (fderiv ℝ (smoothField φ f)) = smoothField φ (fderiv ℝ (fderiv ℝ f)) := by
  rw [fderiv_smoothField φ f (hf.of_le (by norm_num))]
  exact fderiv_smoothField φ _ (hf.fderiv_right (by norm_num))

end OAI.Analysis.Calculus.Coefficients
