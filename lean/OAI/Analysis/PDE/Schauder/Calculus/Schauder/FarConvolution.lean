import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Convolution

/-! Cancellation in the derivative of the smooth far-field convolution. -/

noncomputable section
open _root_.MeasureTheory
namespace OAI.Analysis.PDE.Schauder

theorem integrable_truncated_fderiv {m : ℕ} (hm : 1 ≤ m)
    (v w u : EuclideanSpace ℝ (Fin m)) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y => fderiv ℝ (truncatedNewtonianEntry m v w r) y u) := by
  obtain ⟨C, hC, hbound⟩ := truncatedNewtonianEntry_weighted_fderiv v w
  have hi : Integrable (fun y => ‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖) := by
    simpa using (hbound r 0 volume inferInstance (by simpa using hm) hr zero_lt_one).1
  have hc : Continuous (fun y => fderiv ℝ (truncatedNewtonianEntry m v w r) y u) :=
    ((contDiff_truncatedNewtonianEntry m v w hr).continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hi.mul_const ‖u‖).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => (fderiv ℝ (truncatedNewtonianEntry m v w r) y).le_opNorm u)

theorem fderiv_farConvolution_compensated {m : ℕ} (hm : 1 ≤ m)
    (v w : EuclideanSpace ℝ (Fin m)) {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (scalarConvolution (truncatedNewtonianEntry m v w r) f) x u =
      ∫ y, fderiv ℝ (truncatedNewtonianEntry m v w r) y u * (f (x - y) - f x) := by
  have hK : ContDiff ℝ 1 (truncatedNewtonianEntry m v w r) :=
    (contDiff_truncatedNewtonianEntry m v w hr).of_le (by simp)
  have hc : Continuous (fun y => fderiv ℝ (truncatedNewtonianEntry m v w r) y u) :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgc : HasCompactSupport (fun y => f (x - y)) := hfc.comp_homeomorph (Homeomorph.subLeft x)
  have hi1 : Integrable (fun y => fderiv ℝ (truncatedNewtonianEntry m v w r) y u * f (x - y)) :=
    (hc.mul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hgc.mul_left
  have hi2 := (integrable_truncated_fderiv hm v w u hr).mul_const (f x)
  rw [fderiv_scalarConvolution_kernel _ f hK hf hfc x u]
  simp_rw [mul_sub]
  rw [integral_sub hi1 hi2, integral_mul_const, truncatedNewtonianEntry_fderiv_integral_zero m v w u hr volume,
    zero_mul, sub_zero]

end OAI.Analysis.PDE.Schauder
