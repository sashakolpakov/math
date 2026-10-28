import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BasePartition
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.OneCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOpenConnection
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarOperator

/-! # Scalar Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarCoordinates

noncomputable section

/-! The actual original scalar Chern connection and curvature agree with the literal real coordinate derivative operator wherever the scalar coordinate functions agree. -/

open _root_.ContinuousAlternatingMap Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (U : Opens V.analyticSpace) (f : SmoothScalarForm.SmoothComplexOpenFunction (E := V.analyticModel) U)
  (g : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ)

theorem projectiveScalarChart_real_derivative {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hg : DifferentiableAt ℝ g z)
    (hfg : BasePartition.projectiveScalarChart V e U f =ᶠ[𝓝 z] fun y => (g y : ℂ)) :
    fderiv ℝ (BasePartition.projectiveScalarChart V e U f) z = Complex.ofRealCLM.comp (fderiv ℝ g z) :=
  hfg.fderiv_eq.trans (Complex.ofRealCLM.hasFDerivAt.comp z hg.hasFDerivAt).fderiv

include he in
theorem projectiveScalarConnection_real_coordinates {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) (hg : DifferentiableAt ℝ g z)
    (hfg : BasePartition.projectiveScalarChart V e U f =ᶠ[𝓝 z] fun y => (g y : ℂ)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (ScalarOpenConnection.smoothScalarOpenConnection f).extension z =
      RealScalarOperator.realScalarChernOperator (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (fderiv ℝ g z) := by
  have hd : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)).extension z =
      ofSubsingleton ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) ℂ (0 : Fin 1) (Complex.ofRealCLM.comp (fderiv ℝ g z)) := by
    ext v
    rw [AntiOneFormCoordinates.oneFormLinear_reconstruct, BasePartition.projectiveScalarChart_derivative V e he U f hz,
      projectiveScalarChart_real_derivative V e U f g hg hfg]
    rfl
  rw [ScalarOpenConnection.smoothScalarOpenConnection, OneCoordinates.projectiveOpenChartForm_onePart V e he U (-Complex.I) _ hz, hd]
  ext v
  change (1 / 2 : ℂ) * ((fderiv ℝ g z (v 0) : ℂ) + (-Complex.I) * (fderiv ℝ g z (Complex.I • v 0) : ℂ)) =
    (1 / 2 : ℂ) * ((fderiv ℝ g z (v 0) : ℂ) - Complex.I * (fderiv ℝ g z (Complex.I • v 0) : ℂ))
  ring

include he in
theorem projectiveScalarCurvature_real_coordinates {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) (hg : ContDiff ℝ ∞ g)
    (hfg : BasePartition.projectiveScalarChart V e U f =ᶠ[𝓝 z] fun y => (g y : ℂ)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (ScalarOpenConnection.smoothScalarOpenCurvature f).extension z =
      extDeriv (fun y => RealScalarOperator.realScalarChernOperator (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (fderiv ℝ g y)) z := by
  have hc : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (ScalarOpenConnection.smoothScalarOpenConnection f).extension =ᶠ[𝓝 z]
      fun y => RealScalarOperator.realScalarChernOperator (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (fderiv ℝ g y) := by
    filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e U).isOpen.mem_nhds hz, hfg.eventuallyEq_nhds] with y hy hfy
    exact projectiveScalarConnection_real_coordinates V e he U f g hy (hg.differentiable (by simp) y) hfy
  change Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (ScalarOpenConnection.smoothScalarOpenConnection f)).extension z = _
  rw [ConnectionChartDerivative.projectiveOpenChartForm_d V e he U 1 (ScalarOpenConnection.smoothScalarOpenConnection f) hz]
  unfold extDeriv
  rw [hc.fderiv_eq]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarCoordinates
