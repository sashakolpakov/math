import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Cauchy Kernel -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyKernel

noncomputable section

/-! The genuine locally integrable Cauchy kernel and its smooth convolution operator. -/

open _root_.MeasureTheory _root_.ContinuousLinearMap
open scoped Convolution ContDiff

theorem complex_inv_locallyIntegrable : LocallyIntegrable (fun z : ℂ => z⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · exact Filter.Eventually.of_forall (fun z => by simp [norm_inv, Real.rpow_neg_one])
  · exact measurable_inv.aestronglyMeasurable

def cauchyKernel (z : ℂ) : ℂ := (Real.pi : ℂ)⁻¹ * z⁻¹

theorem cauchyKernel_locallyIntegrable : LocallyIntegrable cauchyKernel volume := by
  exact complex_inv_locallyIntegrable.smul (Real.pi : ℂ)⁻¹

/-- The actual Cauchy integral operator on a compactly supported smooth function. -/
def cauchyTransform (f : ℂ → ℂ) : ℂ → ℂ :=
  cauchyKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f

theorem cauchyTransform_apply (f : ℂ → ℂ) (z : ℂ) :
    cauchyTransform f z = ∫ w : ℂ, cauchyKernel w * f (z - w) := rfl

theorem cauchyTransform_smooth {f : ℂ → ℂ} (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (cauchyTransform f) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) cauchyKernel_locallyIntegrable hf

theorem cauchyTransform_hasFDerivAt {f : ℂ → ℂ} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) (z : ℂ) :
    HasFDerivAt (cauchyTransform f)
      ((cauchyKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ, volume] fderiv ℝ f) z) z :=
  hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyKernel_locallyIntegrable hf z

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyKernel
