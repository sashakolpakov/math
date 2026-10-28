import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantDolbeaultAlternation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ConnectionCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearDolbeaultPullback
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Dolbeault

/-! # Covariant Dolbeault -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Covariant antiholomorphic alternation gives the literal original bundle Dolbeault coordinates in every degree. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem Projective.CovariantDolbeault.projectiveOpenChartForm_pure (U : Opens V.analyticSpace) (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U (p + q)) (ha : Open.ManifoldBidegree.OpenManifoldHasBidegree p q a)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) p q (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (p + q) a.extension z) := by
  intro c v
  change a.extension.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
    (fun i => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((c : ℂ) • v i)) = _
  simp only [map_smul]
  exact ha e he _ hz c (fun i => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V (v i))

theorem Projective.CovariantDolbeault.projectiveOpenChartForm_dolbeault (U : Opens V.analyticSpace) (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U (p + q)) (ha : Open.ManifoldBidegree.OpenManifoldHasBidegree p q a)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (p + q + 1) (Open.ManifoldDolbeault.openManifoldDolbeaultD p q (p + q) a).extension z =
      Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (p + q) a.extension) z := by
  have had := ((a.smooth e he).contDiffAt ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hp := Chern.Complex.LinearDolbeaultPullback.extDerivDoublePrime_complexLinearPullback (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap had
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [Open.ManifoldDolbeault.openManifoldDolbeaultD_eq_local rfl ha e he hz]
  exact hp.symm

variable {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveConnectionChart_holomorphic (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    h.projectiveConnectionChart V e i z (Complex.I • v) = Complex.I * h.projectiveConnectionChart V e i z v := by
  have hp : Open.ManifoldBidegree.OpenManifoldHasBidegree 1 0 (h.localConnection i) :=
    Manifold.OneFormProjection.openManifoldOnePart_holomorphic _
  have hc := Projective.CovariantDolbeault.projectiveOpenChartForm_pure V e he _ 1 0 (h.localConnection i) hp hz AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit (fun _ => v)
  simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, mul_one, AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit_coe] at hc
  exact hc

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveDolbeault_covariant (U : Opens V.analyticSpace) (q : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u U q) (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (q + 1) ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u U q a).val.val i).extension z =
      alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) q)
        (Line.ConnectionSymbols.lineCovectorConnectionDerivative q (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q (a.val.val i).extension) z)) := by
  have hzD : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ⟨hz.1, hz.2.2⟩
  change Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (q + 1) (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 q q (a.val.val i)).extension z = _
  have hd := Projective.CovariantDolbeault.projectiveOpenChartForm_dolbeault V e he
    (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) 0 q
  rw [Nat.zero_add q] at hd
  rw [hd (a.val.val i) (a.property i) hz]
  exact (CovariantDolbeaultAlternation.lineCovectorConnectionDerivative_antilinear_alternation q _ _ _ z
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_symmetric V e he hz.1)
    (ProjectiveLine.Kahler.projectiveLineConnection_twisted_symmetric V e he hz.1)
    (h.projectiveConnectionChart_holomorphic V e he i hzD)).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
