import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.CoefficientPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealFluxRearrangement

/-! # Flux Test -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Exact L² flux rearrangement of the native four-block Bochner equation. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochner_flux_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) (hq : HasCompactSupport q) (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hηone : ∀ x ∈ tsupport q, η x = 1)
    (A : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)
    (hAm : AEStronglyMeasurable A volume) {K : ℝ}
    (hAb : ∀ᵐ x ∂(volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)), ‖A x‖ ≤ K)
    (hAeq : ∀ x ∈ tsupport q, A x = h.projectiveLineSobolevCoefficient V e 1 i x)
    (w f : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (htest : h.projectiveBochnerL2TestFunctional V e he i q hq hsq w = inner ℝ f (q.toLp 2 volume)) :
    ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAb (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) w) (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q)) =
      inner ℝ (f - (h.projectiveLineGradientValueL2 V e he i η hη hηc hηU (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) w)) - (h.projectiveLineWeakValueL2 V e he i η hη hηc hηU (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w))) (q.toLp 2 volume) +
        inner ℝ (-(h.projectiveLineFluxL2 V e he i η hη hηc hηU (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w))) (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q)) :=
  RealFluxRearrangement.real_flux_pair_rearrangement
    (ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAb (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) w) (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q)))
    f (h.projectiveLineGradientValueL2 V e he i η hη hηc hηU (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) w)) (h.projectiveLineWeakValueL2 V e he i η hη hηc hηU (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)) (q.toLp 2 volume)
    (h.projectiveLineFluxL2 V e he i η hη hηc hηU (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)) (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q))
    (Eq.trans (α := ℝ)
      (h.projectiveBochner_coefficient_test_pair V e he i q hq hsq η hη hηc hηU hηone
        A hAm hAb hAeq (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w) (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) w)).symm htest)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
