import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Parameter Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ParameterDerivative

noncomputable section

/-! Smoothness of the actual partial derivative of a smooth parameter-dependent function on an arbitrary open product domain. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def parameterFDerivRight (f : P × E → F) (p : P × E) : E →L[ℝ] F :=
  fderiv ℝ (fun y => f (p.1, y)) p.2

theorem parameterFDerivRight_eq (f : P × E → F) {p : P × E} (hf : DifferentiableAt ℝ f p) :
    parameterFDerivRight f p = (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ P E) := by
  simpa only [Function.comp_def] using!
    (hf.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv

theorem parameterFDerivRight_smoothOn (f : P × E → F) {U : Set (P × E)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (parameterFDerivRight f) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hC : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ P E)) U :=
    hD.clm_comp contDiffOn_const
  apply hC.congr
  intro p hp
  exact parameterFDerivRight_eq f ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ParameterDerivative
