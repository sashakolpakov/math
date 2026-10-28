import OAI.Analysis.Fourier.SquareFunction.KernelHilbert

open OAI.Analysis.Fourier.Wave

/-! Uniform scalar derivative estimates control the concrete radius-valued
derivative. Differentiability is established before taking these bounds. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform

theorem norm_fderiv_continuousMap_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → C(RadiusInterval, ℂ)} (hF : Differentiable ℝ F)
    (x : E) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r : RadiusInterval, ‖fderiv ℝ (fun y => F y r) x‖ ≤ B) :
    ‖fderiv ℝ F x‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg v))).2
  intro r
  have hd : fderiv ℝ (fun y => F y r) x =
      (ContinuousMap.evalCLM ℝ r).comp (fderiv ℝ F x) :=
    (((ContinuousMap.evalCLM ℝ r : C(RadiusInterval, ℂ) →L[ℝ] ℂ)).hasFDerivAt.comp x
      (hF x).hasFDerivAt).fderiv
  have he : (fderiv ℝ (fun y => F y r) x) v = ((fderiv ℝ F x) v) r := by
    rw [hd]
    rfl
  rw [← he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hbound r) (norm_nonneg v))

theorem norm_fderiv_radiusToL2_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → C(RadiusInterval, ℂ)} (hF : Differentiable ℝ F)
    (x : E) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r : RadiusInterval, ‖fderiv ℝ (fun y => F y r) x‖ ≤ B) :
    ‖fderiv ℝ (fun y => radiusToL2 (F y)) x‖ ≤ B := by
  have hd : fderiv ℝ (fun y => radiusToL2 (F y)) x =
      (radiusToL2.restrictScalars ℝ).comp (fderiv ℝ F x) :=
    ((radiusToL2.restrictScalars ℝ).hasFDerivAt.comp x (hF x).hasFDerivAt).fderiv
  have hn := norm_fderiv_continuousMap_le hF x hB hbound
  rw [hd]
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  calc
    ‖((radiusToL2.restrictScalars ℝ).comp (fderiv ℝ F x)) v‖ ≤
        ‖(fderiv ℝ F x) v‖ := norm_radiusToL2_le _
    _ ≤ ‖fderiv ℝ F x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg v)

theorem norm_fderiv_radiusFourierKernel_le {n : ℕ}
    {m : Space n → C(RadiusInterval, ℂ)} (hm : Continuous m) (hc : HasCompactSupport m)
    (x : Space n) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ r : RadiusInterval, ‖fderiv ℝ (𝓕⁻ (fun ξ => m ξ r)) x‖ ≤ B) :
    ‖fderiv ℝ (radiusFourierKernel m) x‖ ≤ B := by
  have hi : Integrable m := hm.integrable_of_hasCompactSupport hc
  apply norm_fderiv_radiusToL2_le (differentiable_fourierInv_compact hm hc) x hB
  intro r
  have he : (fun y => (𝓕⁻ m y) r) = 𝓕⁻ (fun ξ => m ξ r) :=
    funext (fun y => fourierInv_continuousMap_apply hi y r)
  rw [he]
  exact hbound r

end OAI.Analysis.Fourier.SquareFunction
