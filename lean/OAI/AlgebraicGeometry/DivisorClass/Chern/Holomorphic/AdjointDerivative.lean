import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorNeg
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntrinsicKahlerAdjoint

/-! # Adjoint Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The differentiated metric trace is the derivative of the original global Dolbeault adjoint. -/

open Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Holomorphic.AdjointDerivative.lineCovectorConnectionDerivative_congr {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a b : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (hab : a =ᶠ[𝓝 x] b) :
    Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a x = Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A b x := by
  unfold Line.ConnectionSymbols.lineCovectorConnectionDerivative Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative
  rw [hab.fderiv_eq, hab.eq_of_nhds]

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_covector (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension z =
      Line.ConnectionSymbols.lineCovariantCodifferential (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) z := by
  apply (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 0).injective
  change Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension z = _
  rw [h.degreeCodifferential_componentCoefficients V e he i a hz]
  exact h.projectiveCovariantAdjointCoefficients_eq V e he 0 ⊤ a.val i ⟨hz.1, trivial, hz.2⟩

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.degreeCodifferential_covariantDerivative (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
    let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
    let A := h.projectiveConnectionChart V e i
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension
    Line.ConnectionSymbols.lineCovectorConnectionDerivative 0 G A
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension) z v =
      (∑ j, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction 0 (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B z) ((b.coord j).toContinuousLinearMap.comp (G z v)))
        (Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A f z (b j))) -
      ∑ j, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction 0 (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B z) (b.coord j).toContinuousLinearMap)
        (Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A (fun y => Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A f y (b j)) z v) := by
  let D := Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  let W := ConnectionChartDerivative.projectiveOpenChartDomain V e D
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let B := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e
  let G := Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e
  let A := h.projectiveConnectionChart V e i
  let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension
  have heq : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 ((h.degreeCodifferential V 0 a.val).val i).extension =ᶠ[𝓝 z]
      Line.ConnectionSymbols.lineCovariantCodifferential b 0 B G A f := by
    filter_upwards [W.isOpen.mem_nhds hz] with y hy
    exact h.degreeCodifferential_covector V e he i a hy
  have hf : ContDiffOn ℝ ∞ f (W : Set _) :=
    (ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he (⊤ ⊓ D) 1 (a.val.val i)).mono
      (fun _ hy => ⟨hy.1, trivial, hy.2⟩)
  have hd := Line.CovectorNeg.lineCovariantCodifferential_derivative b 0 B G A f W.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hy => hy.1))
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hy => hy.1))
    (h.projectiveConnectionChart_smooth V e he i) hf
    (fun y hy => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hy.1) hz v
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hz.1 v)
  exact (congrArg (fun T => T v) (Holomorphic.AdjointDerivative.lineCovectorConnectionDerivative_congr 0 G A _ _ heq)).trans hd

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
