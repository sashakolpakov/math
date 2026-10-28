import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BasePartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior

/-! # Scalar Exponential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarExponential

noncomputable section

/-! Exact coordinate multiplication and exponential derivatives of original open scalar functions. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (U : Opens V.analyticSpace)

theorem projectiveScalarChart_exp (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    BasePartition.projectiveScalarChart V e U (SmoothScalarExterior.smoothComplexOpenFunctionExp f) z =
      Complex.exp (BasePartition.projectiveScalarChart V e U f z) := by
  rw [BasePartition.projectiveScalarChart_apply V e U _ hz, BasePartition.projectiveScalarChart_apply V e U f hz]
  rfl

theorem projectiveOpenChartForm_scalarMul (n : ℕ)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (SmoothScalarForm.smoothScalarOpenFormMul f a).extension z =
      BasePartition.projectiveScalarChart V e U f z • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n a.extension z := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [SmoothScalarForm.smoothScalarOpenFormMul_inChart f a e hz.2]
  ext v
  rfl

include he

theorem projectiveScalarChart_exp_derivative (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    fderiv ℝ (BasePartition.projectiveScalarChart V e U (SmoothScalarExterior.smoothComplexOpenFunctionExp f)) z v =
      BasePartition.projectiveScalarChart V e U (SmoothScalarExterior.smoothComplexOpenFunctionExp f) z * fderiv ℝ (BasePartition.projectiveScalarChart V e U f) z v := by
  have hd := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1 =>
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.extension z (fun _ => v)) (SmoothScalarExterior.smoothScalarOpenZeroForm_d_exp f)
  rw [projectiveOpenChartForm_scalarMul V e U 1 _ _ hz] at hd
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hd
  have hleft := BasePartition.projectiveScalarChart_derivative V e he U (SmoothScalarExterior.smoothComplexOpenFunctionExp f) hz v
  have hright := BasePartition.projectiveScalarChart_derivative V e he U f hz v
  rw [AntiOneFormCoordinates.oneFormLinear_apply] at hleft hright
  rw [hleft, hright] at hd
  exact hd

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarExponential
