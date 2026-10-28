import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.Functional
import OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCutoffIdentity

/-! # Test Congruence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Exact equality of compact tests transports the native Bochner functional without changing its coefficients. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerL2TestFunctional_congr (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (q r : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) (hq : HasCompactSupport q) (hr : HasCompactSupport r)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (hsr : tsupport r ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hqr : q = r) (w : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    h.projectiveBochnerL2TestFunctional V e he i q hq hsq w =
      h.projectiveBochnerL2TestFunctional V e he i r hr hsr w := by
  subst r
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
