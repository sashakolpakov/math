import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LowerCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.CompactOperatorLpPair

/-! # Forcing Lp Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original weighted projected test gives exactly the constructed adjoint forcing coefficient on L². -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveWeightedAntiSchwartzTest_forcing_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hηone : ∀ x ∈ tsupport g, η x = 1)
    (a : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    inner ℝ a ((h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume) =
      inner ℝ (h.projectiveLineForcingL2 V e he i η hη hηc hηU a)
        ((SchwartzMap.smulLeftCLM _ g c).toLp 2 volume) :=
  CompactOperatorLpPair.compactOperatorSchwartz_L2_pair_of_cutoff (h.projectiveWeightedAntiTestCoefficient V e i)
    (SchwartzMap.smulLeftCLM _ g c)
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
    (h.projectiveWeightedAntiTestCoefficient_smooth V e he i)
    (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_compact g hg c) ((Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_tsupport g c).trans hs)
    η (fun x hx => hηone x (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_tsupport g c hx)) a
    (h.projectiveLineForcingL2 V e he i η hη hηc hηU a)
    (h.projectiveLineForcingL2_coe V e he i η hη hηc hηU a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
