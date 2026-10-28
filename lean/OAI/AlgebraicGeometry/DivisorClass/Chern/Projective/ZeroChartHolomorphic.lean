import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.BasePartition

/-! # Zero Chart Holomorphic -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ZeroChartHolomorphic

noncomputable section

/-! Vanishing of the actual local degree-zero Dolbeault operator makes the literal Euclidean scalar coefficient holomorphic. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (U : Opens V.analyticSpace)

theorem projectiveOpenZeroChart_scalar (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 0)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 a.extension z 0 = Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
  calc
    _ = a.extension.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) 0 :=
      congrArg (a.extension.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) (Subsingleton.elim _ 0)
    _ = _ := Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero_apply a.extension e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)

include he in
theorem projectiveOpenZeroChart_holomorphic (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 0)
    (ha : Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 a = 0) :
    ContDiffOn ℂ ∞ (fun z => Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 a.extension z 0) (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _) := by
  have h := (Holomorphic.ManifoldCoordinates.contMDiffOn_complex_iff_chartCoordinates U (Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a)).mp
    (Manifold.DolbeaultZeroKernel.openManifoldZeroScalar_holomorphic a ha) e he
  have hc := h.comp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.contDiffOn
    (show Set.MapsTo (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V) (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _)
      (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set _) from fun _ hz => hz)
  apply hc.congr
  intro z _
  exact projectiveOpenZeroChart_scalar V e U a z

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ZeroChartHolomorphic
