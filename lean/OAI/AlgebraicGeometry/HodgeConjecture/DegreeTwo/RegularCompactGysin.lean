import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceGysinIntrinsicAdjunction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinAdjunction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularTopGysin

/-! # Regular Compact Gysin -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactGysin.Constructions

noncomputable section

/-!
# The actual local divisor Gysin maps agree with global native compact pushforward

This comparison applies in every complementary degree. The global map uses
native cap duality. Identifying global supported Thom multiplication with
the independent geometric cycle class still requires a separate argument.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

def regularCompactGysin (q r : ℕ) (hs : q+r=2*Z.regularComplexDimension) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) q →ₗ[ℚ]
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) (2*1+q) :=
  LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension •
    (IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward (M := Z.regularAnalyticSpace) (N := Z.regularAmbientSpace)
      (d := Z.regularComplexDimension) (e := V.complexDimension) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)
      q (2*1+q) r hs (SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z q r hs)).hom

variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

theorem regularNormalPairNativeGysin_openSquare (q r : ℕ) (hs : q+r=2*Z.regularComplexDimension) :
    IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward
      (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
      (N := P.openNeighborhood) (d := Z.regularComplexDimension) (e := V.complexDimension)
      (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
      q (2*1+q) r hs (SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z q r hs) ≫
        AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAmbientSpace) P.openNeighborhood (2*1+q) =
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAnalyticSpace)
      (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) q ≫
    IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward (M := Z.regularAnalyticSpace) (N := Z.regularAmbientSpace)
      (d := Z.regularComplexDimension) (e := V.complexDimension) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)
      q (2*1+q) r hs (SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z q r hs) :=
  IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward_openSquare
    (M := Z.regularAnalyticSpace) (N := Z.regularAmbientSpace)
    (d := Z.regularComplexDimension) (e := V.complexDimension)
    (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) P.openNeighborhood
    (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
    (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) (by rfl) q (2*1+q) r hs (SourceGysinIntrinsicAdjunction.Constructions.regularSourceGysinPairingDegree V Z q r hs)

theorem regularCompactGysin_local
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (q r : ℕ) (hs : q+r=2*Z.regularComplexDimension)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)) q) :
    regularCompactGysin V Z q r hs
      (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAnalyticSpace)
        (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) q a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAmbientSpace) P.openNeighborhood (2*1+q)
      (SourceCompactGysin.Constructions.normalPairSourceCompactGysin P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding q a) := by
  rw [SourceGysinIntrinsicAdjunction.Constructions.regularNormalPairSourceCompactGysin_eq_native V Z x P hq hqi q r hs, map_smul]
  exact (congrArg (fun z => LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension • z)
    (ConcreteCategory.congr_hom (regularNormalPairNativeGysin_openSquare V Z x P q r hs) a)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactGysin.Constructions
