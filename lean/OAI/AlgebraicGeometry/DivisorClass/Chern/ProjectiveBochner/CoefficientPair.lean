import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.Functional
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LowerCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.CompactOperatorLpPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.BoundedAdjointLpPair

/-! # Coefficient Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The complete native Bochner pairing is exactly bounded principal energy plus the three actual lower-order L² coefficient pairings. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochner_coefficient_test_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hηone : ∀ x ∈ tsupport q, η x = 1)
    (A : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ]
      GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)
    (hAm : AEStronglyMeasurable A volume) {K : ℝ}
    (hAb : ∀ᵐ x ∂(volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)), ‖A x‖ ≤ K)
    (hAeq : ∀ x ∈ tsupport q, A x = h.projectiveLineSobolevCoefficient V e 1 i x)
    (a : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (d : Lp (GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    inner ℝ d ((h.projectiveBochnerGradientSchwartzTest V e he i q hq hsq).toLp 2 volume) +
      inner ℝ a ((h.projectiveBochnerValueSchwartzTest V e he i q hq hsq).toLp 2 volume) =
      ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAb d (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q)) +
      inner ℝ (h.projectiveLineFluxL2 V e he i η hη hηc hηU a) (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q)) + inner ℝ (h.projectiveLineGradientValueL2 V e he i η hη hηc hηU d) (q.toLp 2 volume) + inner ℝ (h.projectiveLineWeakValueL2 V e he i η hη hηc hηU a) (q.toLp 2 volume) := by
  have hgrad := Compact.SchwartzGradient.compactSchwartzGradient_toLp (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq
  have hA := (BoundedAdjointLpPair.compactAdjointSchwartz_bounded_energy_pair (h.projectiveLineSobolevCoefficient V e 1 i)
    (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineSobolevCoefficient_smooth V e he 1 i) (Compact.SchwartzGradient.compactSchwartzGradient_compact (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) ((Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq).trans hsq)
    A hAm hAb (fun x hx => hAeq x (Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq hx)) d).trans
    (congrArg (ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAb d) hgrad)
  have hB := (CompactOperatorLpPair.compactAdjointSchwartz_L2_pair_of_cutoff (h.projectiveLineValueGradientCoefficient V e 1 i)
    (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineValueGradientCoefficient_smooth V e he 1 i) (Compact.SchwartzGradient.compactSchwartzGradient_compact (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq) ((Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq).trans hsq)
    η (fun x hx => hηone x (Compact.SchwartzGradient.compactSchwartzGradient_tsupport (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq hx)) a (h.projectiveLineFluxL2 V e he i η hη hηc hηU a) (h.projectiveLineFluxL2_coe V e he i η hη hηc hηU a)).trans
    (congrArg (fun v => inner ℝ (h.projectiveLineFluxL2 V e he i η hη hηc hηU a) v) hgrad)
  have hC := CompactOperatorLpPair.compactAdjointSchwartz_L2_pair_of_cutoff (h.projectiveLineGradientValueCoefficient V e 1 i)
    q (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineGradientValueCoefficient_smooth V e he 1 i) hq hsq
    η hηone d (h.projectiveLineGradientValueL2 V e he i η hη hηc hηU d) (h.projectiveLineGradientValueL2_coe V e he i η hη hηc hηU d)
  have hD := CompactOperatorLpPair.compactAdjointSchwartz_L2_pair_of_cutoff (h.projectiveLineWeakValueCoefficient V e i)
    q (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen (h.projectiveLineWeakValueCoefficient_smooth V e he i) hq hsq
    η hηone a (h.projectiveLineWeakValueL2 V e he i η hη hηc hηU a) (h.projectiveLineWeakValueL2_coe V e he i η hη hηc hηU a)
  have hleft := congrArg₂ (fun x y : ℝ => x + y)
    (h.projectiveBochnerGradientSchwartzTest_L2_pair V e he i q hq hsq d)
    (h.projectiveBochnerValueSchwartzTest_L2_pair V e he i q hq hsq a)
  have hp := hleft.trans (congrArg₂ (fun x y : ℝ => x + y)
    (congrArg₂ (fun x y : ℝ => x + y) hA hC) (congrArg₂ (fun x y : ℝ => x + y) hB hD))
  exact hp.trans (SchwartzCutoffIdentity.real_interleave_pair_blocks _ _ _ _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
