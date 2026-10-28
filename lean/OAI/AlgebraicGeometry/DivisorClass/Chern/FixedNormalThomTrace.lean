import OAI.AlgebraicGeometry.DivisorClass.Chern.FixedNormalCover
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomComparison

/-! # Fixed Normal Thom Trace -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FixedNormalThomTrace

noncomputable section

/-! Every compact stage of the actual supported Thom comparison has the original coefficient-one trace in a fixed algebraic normal chart. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomComparison.Constructions
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)
variable (x : D.regularAnalyticSpace)

theorem regularFixedNormalThomStage_compact (K : Compacts (FixedNormalCover.regularFixedSourceOpen D x)) (q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (FixedNormalCover.regularFixedSourceOpen D x))
      (K : Set (FixedNormalCover.regularFixedSourceOpen D x))ᶜ q) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (D.regularFixedNormalPair x).neighborhood)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap (D.regularFixedNormalPair x)
        D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) (2+q)
      ((HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso D a ha x (D.regularFixedNormalPair x) K q).hom b) =
    HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin (D.regularFixedNormalPair x)
      D.isClosedEmbedding_regularComplementInclusion.isEmbedding q
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (FixedNormalCover.regularFixedSourceOpen D x)) K q b) := by
  have hc := ConcreteCategory.congr_hom (HodgeConjecture.DegreeTwo.RegularNormalThomComparison.Constructions.regularNormalSourceThomStageIso_eq_native D a ha x
    (D.regularFixedNormalPair x) (D.regularFixedNormalPair_ambientChart_mdifferentiable x) K q) b
  have hg := HodgeConjecture.DegreeTwo.SourceCompactGysin.Constructions.normalPairSourceCompactGysin_stage_supported (D.regularFixedNormalPair x)
    D.isClosedEmbedding_regularComplementInclusion.isEmbedding K q b
  exact (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
    (TopCat.of (D.regularFixedNormalPair x).neighborhood)
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap (D.regularFixedNormalPair x)
      D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) (2+q)) hc).trans hg.symm

theorem regularFixedNormalThomStage_trace (K : Compacts (FixedNormalCover.regularFixedSourceOpen D x))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (FixedNormalCover.regularFixedSourceOpen D x))
      (K : Set (FixedNormalCover.regularFixedSourceOpen D x))ᶜ (2 * D.regularComplexDimension)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace V.complexDimension (M := (D.regularFixedNormalPair x).openNeighborhood)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (D.regularFixedNormalPair x).neighborhood)) (HodgeConjecture.DegreeTwo.SourceGysinTrace.Constructions.regularSourceGysinTopDegree V D))
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (D.regularFixedNormalPair x).neighborhood)
          (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap (D.regularFixedNormalPair x)
            D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) (2 + 2 * D.regularComplexDimension)
          ((HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso D a ha x (D.regularFixedNormalPair x) K
            (2 * D.regularComplexDimension)).hom b))) =
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace D.regularComplexDimension (M := FixedNormalCover.regularFixedSourceOpen D x)
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (FixedNormalCover.regularFixedSourceOpen D x)) K
        (2 * D.regularComplexDimension) b) := by
  rw [regularFixedNormalThomStage_compact]
  have h := HodgeConjecture.DegreeTwo.SourceGysinTrace.Constructions.regularNormalPairSourceCompactGysin_topTrace V D x (D.regularFixedNormalPair x)
    (FixedNormalCover.regularFixedNormalPair_contMDiffOn D x) (FixedNormalCover.regularFixedNormalPair_symm_contMDiffOn D x)
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (FixedNormalCover.regularFixedSourceOpen D x)) K
      (2 * D.regularComplexDimension) b)
  simpa only [LocalProductCoefficientOne.localProductCupCoefficient_line, mul_one] using! h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FixedNormalThomTrace
