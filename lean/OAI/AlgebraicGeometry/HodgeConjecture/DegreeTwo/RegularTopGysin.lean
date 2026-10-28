import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicTopOpenSquare
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedNormalTopGysin
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceSupport

/-! # Regular Top Gysin -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions

noncomputable section

/-!
# Global top-degree pushforward and the actual local divisor Gysin maps

The global map is defined using native cap duality. The local normal-pair
construction agrees with this map after open extension. This identifies
top-degree Gysin outputs; the global Thom cup comparison remains separate.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

abbrev regularSourceInclusionMap : TopCat.of Z.regularAnalyticSpace ⟶ TopCat.of Z.regularAmbientSpace :=
  TopCat.ofHom ⟨Z.regularComplementInclusion,Z.continuous_regularComplementInclusion⟩

def regularTopGysin :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (2*Z.regularComplexDimension) →ₗ[ℚ]
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) (2*V.complexDimension) :=
  LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension •
    (IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward (M := Z.regularAnalyticSpace) (N := Z.regularAmbientSpace)
      (d := Z.regularComplexDimension) (e := V.complexDimension) (regularSourceInclusionMap V Z)).hom

variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

abbrev regularNormalPairNativeTopPushforward :=
  IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward
    (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
    (N := P.openNeighborhood) (d := Z.regularComplexDimension) (e := V.complexDimension)
    (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)

theorem regularNormalPairSourceGysinNative_eq_topPushforward
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2*Z.regularComplexDimension)) :
    NestedNormalTopGysin.Constructions.regularNormalPairSourceGysinNative V Z x P a =
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension •
        regularNormalPairNativeTopPushforward V Z x P a := by
  apply NormalPairTraceInjective.Constructions.normalPair_nativeTrace_injective P
    ((Nat.add_comm 1 Z.regularComplexDimension).trans Z.regularComplexDimension_add_codimension)
  have hL := RegularLocalGysinTrace.Constructions.regularNormalPairSourceGysin_nativeTrace V Z x P hq hqi a
  have hR := ConcreteCategory.congr_hom
    (IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward_trace
      (M := NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
      (N := P.openNeighborhood) (d := Z.regularComplexDimension) (e := V.complexDimension)
      (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)) a
  rw [map_smul]
  exact hL.trans ((mul_comm _ _).trans
    (congrArg (fun z => LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension * z) hR.symm))

theorem regularNormalPairNativeTopPushforward_openSquare :
    regularNormalPairNativeTopPushforward V Z x P ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAmbientSpace) P.openNeighborhood (2*V.complexDimension) =
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAnalyticSpace)
      (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
      (2*Z.regularComplexDimension) ≫
    IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward (M := Z.regularAnalyticSpace) (N := Z.regularAmbientSpace)
      (d := Z.regularComplexDimension) (e := V.complexDimension) (regularSourceInclusionMap V Z) :=
  IntrinsicTopOpenSquare.Constructions.nativeTopCohomologyPushforward_openSquare
    (M := Z.regularAnalyticSpace) (N := Z.regularAmbientSpace)
    (d := Z.regularComplexDimension) (e := V.complexDimension)
    (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) P.openNeighborhood
    (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
    (regularSourceInclusionMap V Z) (by rfl)

theorem regularTopGysin_local
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2*Z.regularComplexDimension)) :
    RegularLocalGysinTrace.Constructions.regularNormalPairSourceGysinToAmbient V Z x P a =
      regularTopGysin V Z
        (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAnalyticSpace)
          (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding)
          (2*Z.regularComplexDimension) a) := by
  let extP := AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAmbientSpace)
    P.openNeighborhood (2*V.complexDimension)
  have hL := congrArg extP (regularNormalPairSourceGysinNative_eq_topPushforward V Z x P hq hqi a)
  have hS := map_smul extP.hom (LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension)
    (regularNormalPairNativeTopPushforward V Z x P a)
  have hG := ConcreteCategory.congr_hom (regularNormalPairNativeTopPushforward_openSquare V Z x P) a
  exact hL.trans (hS.trans
    (congrArg (fun z => LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension • z) hG))

theorem regularTopGysin_trace
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := Z.regularAmbientSpace) (regularTopGysin V Z a) =
      LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension *
        AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := Z.regularAnalyticSpace) a := by
  have h := ConcreteCategory.congr_hom (IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward_trace
    (M := Z.regularAnalyticSpace) (N := Z.regularAmbientSpace)
    (d := Z.regularComplexDimension) (e := V.complexDimension) (regularSourceInclusionMap V Z)) a
  change AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := Z.regularAmbientSpace)
    (LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension •
      IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward (M := Z.regularAnalyticSpace) (N := Z.regularAmbientSpace)
        (d := Z.regularComplexDimension) (e := V.complexDimension) (regularSourceInclusionMap V Z) a) = _
  rw [map_smul]
  exact congrArg (fun z => LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension * z) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions
