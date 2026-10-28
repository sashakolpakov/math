import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalProductCoefficientOne
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalCoordinateIntegration

/-! # Normalized Local Gysin -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.NormalizedLocalGysin

noncomputable section

/-!
# ChernClass: actual divisor normal-pair Gysin maps have the native normalization

The original local cup coefficient is now one in every tangent dimension.
The previously proved local adjunction therefore identifies the actual
normal-pair Thom Gysin map with the independent native cap pushforward,
without a scalar ambiguity. This is a local statement; the global Thom
class comparison remains a separate gluing step.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem normalLineSupportedCupTop_trace (d : ℕ) (K : Compacts (Fin d → ℂ))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin 1 → ℂ) × (Fin d → ℂ)))
      (Prod.snd ⁻¹' (K : Set (Fin d → ℂ))ᶜ) (2 * d)) :
    HodgeConjecture.DegreeTwo.CompactProductTrace.Constructions.compactProductCoordinateTrace 1 d (HodgeConjecture.DegreeTwo.NormalCoordinateIntegration.Constructions.normalCoordinateSupportedCupTop 1 d K b) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := Fin d → ℂ) (HodgeConjecture.DegreeTwo.NormalCoordinateIntegration.Constructions.normalCoordinateTestRestriction 1 d K b) := by
  rw [HodgeConjecture.DegreeTwo.NormalCoordinateIntegration.Constructions.normalCoordinateSupportedCupTop_trace, LocalProductCoefficientOne.localProductCupCoefficient_line, mul_one]

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

theorem regularNormalPairSourceCompactGysin_native
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (q r : ℕ) (hs : q + r = 2 * Z.regularComplexDimension)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)) q) :
    HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding q a =
      HodgeConjecture.DegreeTwo.IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward
        (M := HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
        (N := P.openNeighborhood) (d := Z.regularComplexDimension) (e := V.complexDimension)
        (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
        q (2 * 1 + q) r hs (HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z q r hs) a := by
  rw [HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction.Constructions.regularNormalPairSourceCompactGysin_eq_native V Z x P hq hqi q r hs,
    LocalProductCoefficientOne.localProductCupCoefficient_line, one_smul]

theorem regularNormalPairSourceCompactGysin_native_adjunction
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (q r : ℕ) (hs : q + r = 2 * Z.regularComplexDimension)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)) q)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) r) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (M := P.openNeighborhood) r (2 * 1 + q)
      (by have h := HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z q r hs; omega) b
      (HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding q a) =
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation Z.regularComplexDimension
        (M := HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) r q (by omega)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
          (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) r b) a := by
  rw [HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction.Constructions.regularNormalPairSourceCompactGysin_adjunction V Z x P hq hqi q r hs,
    LocalProductCoefficientOne.localProductCupCoefficient_line, mul_one]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.NormalizedLocalGysin
