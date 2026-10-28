import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.KahlerCommutator
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Connection
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnection

/-! # Kahler -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The local Kähler identity on the original bundle frames with the actual projective and line connections. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveConnectionChart (i : V.analyticSpace) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℂ :=
  AntiOneFormCoordinates.oneFormLinear (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (h.localConnection i).extension z)

include he

theorem ProjectiveLine.Kahler.projectiveLineConnection_twisted_symmetric {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (v w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z (Complex.I • v) w =
      Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z (Complex.I • w) v := by
  rw [Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_left V e he hz,
    Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_left V e he hz,
    Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_symmetric V e he hz v w]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveKahler_zero (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction 0 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
      (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
      (Line.ConnectionSymbols.lineTwistedExteriorDerivative 1 (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
        (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) z) =
      Line.ConnectionSymbols.lineCovariantCodifferential (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
        (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) z := by
  have hz' : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := hz.1
  exact Line.KahlerCommutator.lineKahlerCommutator_zero (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) z
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz') (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz')
    (Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz') (ProjectiveLine.Kahler.projectiveLineConnection_twisted_symmetric V e he hz')

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveKahler (n : ℕ) (U : Opens V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U (n + 1 + 1)) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction (n + 1) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
        (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
        (Line.ConnectionSymbols.lineTwistedExteriorDerivative (n + 1 + 1) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
          (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) (a.val i).extension) z) -
      Line.ConnectionSymbols.lineTwistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (h.projectiveConnectionChart V e i)
        (fun y => Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y)
          (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) (a.val i).extension y)) z =
      Line.ConnectionSymbols.lineCovariantCodifferential (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (n + 1)
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
        (h.projectiveConnectionChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) (a.val i).extension) z := by
  let W := U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  have hsub := ConnectionChartDerivative.projectiveOpenChartDomain_le V e W
  have hz' : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := hsub hz
  exact Line.KahlerCommutator.lineKahlerCommutator (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1 + 1) (a.val i).extension) (ConnectionChartDerivative.projectiveOpenChartDomain V e W).isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono hsub)
    (fun y hy => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he (hsub hy)) hz
    (ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he W (n + 1 + 1) (a.val i))
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz') (Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz')
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hz') (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_J_right V e he hz')
    (ProjectiveLine.Kahler.projectiveLineConnection_twisted_symmetric V e he hz')

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
