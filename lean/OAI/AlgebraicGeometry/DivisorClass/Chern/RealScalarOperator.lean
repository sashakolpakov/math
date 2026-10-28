import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOneFormDerivative
import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts

/-! # Real Scalar Operator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarOperator

noncomputable section

/-! The original complex-linear part of a real scalar differential, as a bounded one-form operator, and its exact curvature sign. -/

open _root_.ContinuousAlternatingMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def realScalarChernOperator : (E →L[ℝ] ℝ) →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ).restrictScalars ℝ).comp
      (ContinuousLinearMap.compL ℝ E ℝ ℂ Complex.ofRealCLM))

theorem realScalarChernOperator_apply (D : E →L[ℝ] ℝ) (v : Fin 1 → E) :
    realScalarChernOperator E D v = (1 / 2 : ℂ) * ((D (v 0) : ℂ) - Complex.I * (D (Complex.I • v 0) : ℂ)) := rfl

theorem realScalarChernOperator_curvature_re (D : E →L[ℝ] (E →L[ℝ] ℝ)) (v : E) :
    (Complex.I * (realScalarChernOperator E (D v) (fun _ => Complex.I • v) -
      realScalarChernOperator E (D (Complex.I • v)) (fun _ => v))).re =
      -(1 / 2 : ℝ) * (D v v + D (Complex.I • v) (Complex.I • v)) := by
  rw [realScalarChernOperator_apply, realScalarChernOperator_apply]
  have hII : Complex.I • (Complex.I • v) = -v := by simp [smul_smul]
  rw [hII, map_neg]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  norm_num
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarOperator
