import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomStageRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalImageStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportRepresentative

/-! # Compact Normal Stage Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactNormalStageComparison.Constructions

noncomputable section

/-! The restriction of the global compact construction is the independently constructed supported Gysin stage in each smooth normal chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)
variable (x : Z.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)

theorem regularNormalCompactComplement_restrict (K : Compacts (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) :
    (Opens.map (Opens.inclusion' (X := TopCat.of Z.regularAmbientSpace) P.openNeighborhood)).obj
      (RegularCompactThomStage.Constructions.regularCompactImageComplement Z (CompactThomStageRestriction.Constructions.regularLocalCompactSourceImage Z P.openNeighborhood K)) =
    NormalSupportRelative.Constructions.normalPairImageComplementOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K := by
  apply Opens.ext
  exact CompactImageOpenRestriction.Constructions.compactImage_openPreimage_complement (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) P.openNeighborhood K

theorem regularSourceLocalCompactThomStageIso_normalPair_eq_image
    (K : Compacts (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) (q : ℕ) :
    (CompactThomStageRestriction.Constructions.regularSourceLocalCompactThomStageIso Z P.openNeighborhood a ha K q).hom =
      (RegularNormalImageStage.Constructions.regularNormalSourceImageStageIso Z a ha x P K q).hom := by
  exact LocalSupportRepresentative.Constructions.regularSourceThomLocalSupportIso_ambient_restriction_cast Z a ha P.openNeighborhood
    (RegularCompactThomStage.Constructions.regularCompactImageComplement Z (CompactThomStageRestriction.Constructions.regularLocalCompactSourceImage Z P.openNeighborhood K))
    (NormalSupportRelative.Constructions.normalPairImageComplementOpen P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K)
    (regularNormalCompactComplement_restrict Z x P K)
    (K : Set (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P))ᶜ
    (OpenEmbeddingExtension.Constructions.embeddingCompactImage (NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P
      Z.isClosedEmbedding_regularComplementInclusion.isEmbedding) K : Set P.neighborhood)ᶜ q
    (CompactThomStageRestriction.Constructions.regularLocalCompactSourceComplement Z P.openNeighborhood K)
    (CompactThomStageRestriction.Constructions.regularLocalCompactTargetComplement Z P.openNeighborhood K)
    (NormalSupportRelative.Constructions.normalPairImageComplement_source P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K)
    (NormalSupportRelative.Constructions.normalPairImage_union_complement P Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K)

theorem regularSourceLocalCompactThomStageIso_normalPair_eq_native
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)))
    (K : Compacts (RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x P)) (q : ℕ) :
    (CompactThomStageRestriction.Constructions.regularSourceLocalCompactThomStageIso Z P.openNeighborhood a ha K q).hom =
      ModuleCat.ofHom (SourceSupportedThomIso.Constructions.normalPairSourceSupportedCohomologyIso P
        Z.isClosedEmbedding_regularComplementInclusion.isEmbedding K q).toLinearMap :=
  (regularSourceLocalCompactThomStageIso_normalPair_eq_image Z a ha x P K q).trans
    (RegularNormalImageStage.Constructions.regularNormalSourceImageStageIso_eq_native Z a ha x P hP K q)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactNormalStageComparison.Constructions
