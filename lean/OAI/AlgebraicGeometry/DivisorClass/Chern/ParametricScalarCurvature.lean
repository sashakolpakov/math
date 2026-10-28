import OAI.AlgebraicGeometry.DivisorClass.Chern.ParameterDerivative
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarOperator

/-! # Parametric Scalar Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricScalarCurvature

noncomputable section

/-! Actual scalar Chern curvature depends smoothly on both its parameter and coordinate on every domain where the original potential does. -/

open _root_.ContinuousAlternatingMap
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem parametricScalarChernCurvature_smoothOn (f : P × E → ℝ) {U : Set (P × E)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun p : P × E => extDeriv
      (fun y => RealScalarOperator.realScalarChernOperator E (fderiv ℝ (fun z => f (p.1, z)) y)) p.2) U := by
  have hA : ContDiffOn ℝ ∞ (fun p => RealScalarOperator.realScalarChernOperator E (ParameterDerivative.parameterFDerivRight f p)) U :=
    (ParameterDerivative.parameterFDerivRight_smoothOn f hU hf).continuousLinearMap_comp (RealScalarOperator.realScalarChernOperator E)
  exact (ParameterDerivative.parameterFDerivRight_smoothOn _ hU hA).continuousLinearMap_comp (alternatizeUncurryFinCLM ℝ E ℂ)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricScalarCurvature
