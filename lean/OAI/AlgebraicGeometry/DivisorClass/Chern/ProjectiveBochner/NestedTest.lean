import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.TestSupport
import OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzLpLocality
import OAI.Analysis.HodgeTheory.Decomposition.VectorNestedCutoffs
import OAI.Analysis.HodgeTheory.Decomposition.PairLocality

/-! # Nested Test -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! An actual outer Sobolev cutoff equal to one near the test leaves the entire native Bochner functional unchanged. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerL2TestFunctional_nested (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) (hq : HasCompactSupport q) (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (ψ : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (hψ : ∀ x ∈ tsupport q, (ψ : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[nhds x] 1)
    (w : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    h.projectiveBochnerL2TestFunctional V e he i q hq hsq (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ w) =
      h.projectiveBochnerL2TestFunctional V e he i q hq hsq w :=
  congrArg₂ (fun x y : ℝ => x + y)
    (SchwartzLpLocality.lp_schwartz_inner_eq_on (h.projectiveBochnerGradientSchwartzTest V e he i q hq hsq)
      (tsupport q) (h.projectiveBochnerGradientSchwartzTest_zero_off V e he i q hq hsq)
      (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ w)) (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) w)
      (Analysis.HodgeTheory.Decomposition.VectorNestedCutoffs.Constructions.vectorSobolevGradient_cutoff_eq_on (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) ψ hψ w))
    (SchwartzLpLocality.lp_schwartz_inner_eq_on (h.projectiveBochnerValueSchwartzTest V e he i q hq hsq)
      (tsupport q) (h.projectiveBochnerValueSchwartzTest_zero_off V e he i q hq hsq)
      (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ w)) (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)
      (Analysis.HodgeTheory.Decomposition.PairLocality.Constructions.vectorSobolevL2Embedding_cutoff_eq_on ψ (fun x hx => (hψ x hx).eq_of_nhds) w))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
