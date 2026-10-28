import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.WeightedSchwartzTests

/-! # Weighted Schwartz Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The weighted compact test represents the original antiholomorphic metric pairing in ordinary real Hilbert coordinates. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Projective.WeightedSchwartzPair.covectorAntiProjectionCoordinates_smul
    {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι] [LinearOrder ι]
    (b : Module.Basis ι ℝ E) (r : ℂ) (c : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι 1) :
    CovectorPairCoefficient.covectorOperatorCoordinates b 1 OneCovectorAntiProjection.oneCovectorAntiProjection (r • c) =
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1 (r • OneCovectorAntiProjection.oneCovectorAntiProjection ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1).symm c)) := by
  change Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1 (OneCovectorAntiProjection.oneCovectorAntiProjection ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1).symm (r • c))) = _
  rw [map_smul, OneCovectorAntiProjection.oneCovectorAntiProjection_complex_smul]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiSchwartzTest_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    inner ℝ (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1 a) (h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c z) =
      (Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
        (fun _ => a) (fun _ => g z • OneCovectorAntiProjection.oneCovectorAntiProjection ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1).symm (c z))) z).re := by
  dsimp only
  rw [h.projectiveWeightedAntiSchwartzTest_apply V e he i g hg hs c z,
    HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiTestCoefficient, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, Projective.WeightedSchwartzPair.covectorAntiProjectionCoordinates_smul]
  exact h.projectiveLinePairCoefficient_pair V e 1 i hz a _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
