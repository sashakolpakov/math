import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.Functional

/-! # Test Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Both actual Bochner adjoint tests vanish off the support of the original compact test. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerGradientSchwartzTest_zero_off (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) (hq : HasCompactSupport q) (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∉ tsupport q) :
    h.projectiveBochnerGradientSchwartzTest V e he i q hq hsq x = 0 := by
  rw [h.projectiveBochnerGradientSchwartzTest_apply V e he i q hq hsq x,
    image_eq_zero_of_notMem_tsupport (fun ht => hx (Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq ht)),
    image_eq_zero_of_notMem_tsupport hx, map_zero, map_zero, add_zero]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerValueSchwartzTest_zero_off (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) (hq : HasCompactSupport q) (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∉ tsupport q) :
    h.projectiveBochnerValueSchwartzTest V e he i q hq hsq x = 0 := by
  rw [h.projectiveBochnerValueSchwartzTest_apply V e he i q hq hsq x,
    image_eq_zero_of_notMem_tsupport (fun ht => hx (Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq ht)),
    image_eq_zero_of_notMem_tsupport hx, map_zero, map_zero, add_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
