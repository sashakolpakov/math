import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairTraceInjective
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedOpenTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularLocalGysinTrace

/-! # Nested Normal Top Gysin -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedNormalTopGysin.Constructions

noncomputable section

/-!
# DegreeTwo: top local Gysin maps agree across different nested normal charts

The ambient and source traces are both native. Injectivity of the target
normal neighborhood's top trace proves equality of the actual compact
classes. This statement is local in top degree; it is not a global cup
comparison or an all-degree descent theorem.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

def regularNormalPairSourceGysinNative (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2*Z.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) (2*V.complexDimension) :=
  eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
    (RegularLocalGysinTrace.Constructions.regularNormalPairDegreeEq V Z))
    (RegularLocalGysinTrace.Constructions.normalPairSourceCompactGysinTop P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding a)

variable {x y : Z.regularAnalyticSpace}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)
variable (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion y)
variable (hPQ : P.neighborhood ⊆ Q.neighborhood)

include hPQ in
theorem regularNormalPairNestedSourceLE :
    NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding ≤
      NormalPairProductSupport.Constructions.normalPairSourceOpen Q Z.isClosedEmbedding_regularComplementInclusion.isEmbedding :=
  fun _ hz => hPQ hz

abbrev regularNormalPairNestedAmbientMap : TopCat.of P.neighborhood ⟶ TopCat.of Q.neighborhood :=
  NestedOpenPointClass.Constructions.opensInclusionMap (X := TopCat.of Z.regularAmbientSpace)
    (U := P.openNeighborhood) (V := Q.openNeighborhood) hPQ

abbrev regularNormalPairNestedSourceMap :
    TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) ⟶
    TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen Q Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) :=
  NestedOpenPointClass.Constructions.opensInclusionMap (X := TopCat.of Z.regularAnalyticSpace) (regularNormalPairNestedSourceLE V Z P Q hPQ)

theorem regularNormalPairNestedTopGysin_eq
    (hp : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hpi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ P.ambientChart.symm P.ambientChart.target)
    (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)) ∞ Q.ambientChart Q.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))
      𝓘(ℂ, V.analyticModel) ∞ Q.ambientChart.symm Q.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding))
      (2*Z.regularComplexDimension)) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (regularNormalPairNestedAmbientMap V Z P Q hPQ)
      (NestedOpenPointClass.Constructions.opensInclusionMap_isOpenEmbedding (X := TopCat.of Z.regularAmbientSpace)
        (U := P.openNeighborhood) (V := Q.openNeighborhood) hPQ) (2*V.complexDimension)
      (regularNormalPairSourceGysinNative V Z x P a) =
    regularNormalPairSourceGysinNative V Z y Q
      (OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (regularNormalPairNestedSourceMap V Z P Q hPQ)
        (NestedOpenPointClass.Constructions.opensInclusionMap_isOpenEmbedding (X := TopCat.of Z.regularAnalyticSpace)
          (regularNormalPairNestedSourceLE V Z P Q hPQ)) (2*Z.regularComplexDimension) a) := by
  apply NormalPairTraceInjective.Constructions.normalPair_nativeTrace_injective Q
    ((Nat.add_comm 1 Z.regularComplexDimension).trans Z.regularComplexDimension_add_codimension)
  let b := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (regularNormalPairNestedSourceMap V Z P Q hPQ)
    (NestedOpenPointClass.Constructions.opensInclusionMap_isOpenEmbedding (X := TopCat.of Z.regularAnalyticSpace)
      (regularNormalPairNestedSourceLE V Z P Q hPQ)) (2*Z.regularComplexDimension) a
  have hA := ConcreteCategory.congr_hom
    (NestedOpenTrace.Constructions.complexManifoldTrace_openInclusion (p := V.complexDimension) (M := Z.regularAmbientSpace)
      (U := P.openNeighborhood) (V := Q.openNeighborhood) hPQ)
    (regularNormalPairSourceGysinNative V Z x P a)
  have hS := ConcreteCategory.congr_hom
    (NestedOpenTrace.Constructions.complexManifoldTrace_openInclusion (p := Z.regularComplexDimension) (M := Z.regularAnalyticSpace)
      (regularNormalPairNestedSourceLE V Z P Q hPQ)) a
  have hP := RegularLocalGysinTrace.Constructions.regularNormalPairSourceGysin_nativeTrace V Z x P hp hpi a
  have hQ := RegularLocalGysinTrace.Constructions.regularNormalPairSourceGysin_nativeTrace V Z y Q hq hqi b
  exact (hA.trans hP).trans
    (hQ.trans (congrArg (fun z => z * LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension) hS)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedNormalTopGysin.Constructions
