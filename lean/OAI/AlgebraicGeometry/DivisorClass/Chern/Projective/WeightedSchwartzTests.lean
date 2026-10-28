import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvatureCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiProjection
import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful

/-! # Weighted Schwartz Tests -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Compact weighted antiholomorphic tests in the exact Euclidean Hilbert coordinates of the original metric. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiTestCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ]
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 :=
  (h.projectiveLinePairCoefficient V e 1 i z).adjoint.comp
    (CovectorPairCoefficient.covectorOperatorCoordinates (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 OneCovectorAntiProjection.oneCovectorAntiProjection)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiTestCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveWeightedAntiTestCoefficient V e i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) := by
  let F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1
  have hAdj : ContDiff ℝ ∞ (ContinuousLinearMap.adjoint : (F →L[ℝ] F) → F →L[ℝ] F) :=
    (ContinuousLinearMap.adjoint : (F →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] F)).toContinuousLinearEquiv.contDiff
  exact (hAdj.comp_contDiffOn (h.projectiveLinePairCoefficient_smooth V e he 1 i)).clm_comp contDiffOn_const

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiSchwartzTest (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :
    𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) :=
  Compact.Adjoint.compactOperatorSchwartz (h.projectiveWeightedAntiTestCoefficient V e i) (SchwartzMap.smulLeftCLM _ g c)
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
    (h.projectiveWeightedAntiTestCoefficient_smooth V e he i)
    (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_compact g hg c) ((Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_tsupport g c).trans hs)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiSchwartzTest_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c z =
      h.projectiveWeightedAntiTestCoefficient V e i z (g z • c z) := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiSchwartzTest, Compact.Adjoint.compactOperatorSchwartz_apply,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiSchwartzTest_tsupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :
    tsupport (h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c) ⊆ tsupport g :=
  (Compact.Adjoint.operator_apply_tsupport (h.projectiveWeightedAntiTestCoefficient V e i)
    (SchwartzMap.smulLeftCLM _ g c)).trans (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_tsupport g c)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
