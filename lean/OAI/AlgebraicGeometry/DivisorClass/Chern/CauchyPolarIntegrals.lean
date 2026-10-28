import OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Cauchy Polar Integrals -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarIntegrals

noncomputable section

/-! The radial fundamental theorem and cancellation of the angular derivative. -/

open _root_.MeasureTheory _root_.Complex
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem polarUnit_continuous : Continuous CauchyPolarCalculus.polarUnit := continuous_circleMap 0 1

theorem polarUnit_endpoints : CauchyPolarCalculus.polarUnit Real.pi = CauchyPolarCalculus.polarUnit (-Real.pi) := by
  simp [CauchyPolarCalculus.polarUnit, circleMap, Complex.exp_mul_I]

theorem polarRadialDerivative_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun p : ℝ × ℝ => fderiv ℝ f (p.1 • CauchyPolarCalculus.polarUnit p.2) (CauchyPolarCalculus.polarUnit p.2)) :=
  ((hf.continuous_fderiv (by simp)).comp
    (continuous_fst.smul (polarUnit_continuous.comp continuous_snd))).clm_apply
      (polarUnit_continuous.comp continuous_snd)

theorem polarAngularDerivative_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun p : ℝ × ℝ => fderiv ℝ f (p.1 • CauchyPolarCalculus.polarUnit p.2) (I * CauchyPolarCalculus.polarUnit p.2)) :=
  ((hf.continuous_fderiv (by simp)).comp
    (continuous_fst.smul (polarUnit_continuous.comp continuous_snd))).clm_apply
      ((polarUnit_continuous.comp continuous_snd).const_mul I)

theorem integral_polarRadialDerivative {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (R θ : ℝ) :
    (∫ r in (0 : ℝ)..R, fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (CauchyPolarCalculus.polarUnit θ)) =
      f (R • CauchyPolarCalculus.polarUnit θ) - f 0 := by
  have hd : Continuous (fun r : ℝ => fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (CauchyPolarCalculus.polarUnit θ)) :=
    (polarRadialDerivative_continuous hf).comp (continuous_id.prodMk continuous_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := R)
    (fun r _ => CauchyPolarCalculus.polarRadial_hasDerivAt (hf.differentiable (by simp)) r θ)
    (hd.intervalIntegrable 0 R)
  simpa only [zero_smul] using h

theorem integral_polarAngularDerivative {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    {r : ℝ} (hr : r ≠ 0) :
    (∫ θ in (-Real.pi)..Real.pi, fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (I * CauchyPolarCalculus.polarUnit θ)) = 0 := by
  have hd : Continuous (fun θ : ℝ => fderiv ℝ f (r • CauchyPolarCalculus.polarUnit θ) (I * CauchyPolarCalculus.polarUnit θ)) :=
    (polarAngularDerivative_continuous hf).comp (continuous_const.prodMk continuous_id)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -Real.pi) (b := Real.pi)
    (fun θ _ => CauchyPolarCalculus.polarAngular_hasDerivAt (hf.differentiable (by simp)) r θ)
    ((hd.const_smul r).intervalIntegrable (-Real.pi) Real.pi)
  rw [intervalIntegral.integral_smul, polarUnit_endpoints, sub_self] at h
  exact (smul_eq_zero_iff_right hr).mp h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarIntegrals
