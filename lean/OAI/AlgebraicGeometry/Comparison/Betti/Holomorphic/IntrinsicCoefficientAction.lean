import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModules
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntrinsicFunctionSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormFrames

/-! # Intrinsic Coefficient Action -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntrinsicCoefficientAction

noncomputable section

/-! The standard manifold-function action is the original coordinate coefficient action. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem nativeFunction_smul_eq (U : Opens E) (n : ℕ) (f : FunctionPure.holomorphicFunctions U)
    (a : DeRhamComplex.forms E U n) : IntrinsicFunctionSheaf.holomorphicFunctionContMDiffEquiv U f • a = f • a := by
  apply HolomorphicPullback.inclusion_injective n
  apply (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm.injective
  ext x v
  rw [FormFrames.forms_function_smul_coefficients]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntrinsicCoefficientAction
