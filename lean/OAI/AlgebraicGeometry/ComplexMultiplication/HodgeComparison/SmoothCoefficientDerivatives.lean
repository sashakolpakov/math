import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientExtension

/-! # Smooth Coefficient Derivatives -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientDerivatives.CM.Construction

noncomputable section

/-! Derivatives of a smooth coefficient field which is constant off a compact
set are compactly supported, smooth, bounded, and Lipschitz. -/

open Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem coefficientDerivative_smooth (A : E → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (m : E) : ContDiff ℝ ∞ (CoefficientDerivative.CM.Construction.coefficientDerivative A m) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ A) := hA.fderiv_right (by simp)
  exact hD.clm_apply contDiff_const

theorem coefficientDerivative_compact_support (A : E → F →L[ℝ] F) (c : F →L[ℝ] F)
    (hc : HasCompactSupport (fun x => A x - c)) (m : E) :
    HasCompactSupport (CoefficientDerivative.CM.Construction.coefficientDerivative A m) := by
  have h : HasCompactSupport (fun x => fderiv ℝ (fun y => A y - c) x m) :=
    (hc.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] F →L[ℝ] F => T m)
      (show (0 : E →L[ℝ] F →L[ℝ] F) m = 0 from rfl)
  change HasCompactSupport (fun x => fderiv ℝ A x m)
  simpa only [fderiv_sub_const] using h

theorem coefficientDerivative_lipschitz (A : E → F →L[ℝ] F) (c : F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c)) (m : E) :
    ∃ L : NNReal, LipschitzWith L (CoefficientDerivative.CM.Construction.coefficientDerivative A m) :=
  SmoothCoefficientExtension.CM.Construction.compact_smooth_lipschitz (CoefficientDerivative.CM.Construction.coefficientDerivative A m) (coefficientDerivative_smooth A hA m)
    (coefficientDerivative_compact_support A c hc m)

theorem smoothCoefficientExtension_derivative_lipschitz
    (η : E → ℝ) (A : E → F →L[ℝ] F)
    (hsmooth : ContDiff ℝ ∞ (SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension η A))
    (hη : HasCompactSupport η) (m : E) :
    ∃ L : NNReal, LipschitzWith L (CoefficientDerivative.CM.Construction.coefficientDerivative (SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension η A) m) :=
  coefficientDerivative_lipschitz _ (ContinuousLinearMap.id ℝ F) hsmooth
    (SmoothCoefficientExtension.CM.Construction.smoothCoefficientExtension_compact_perturbation η A hη) m

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientDerivatives.CM.Construction
