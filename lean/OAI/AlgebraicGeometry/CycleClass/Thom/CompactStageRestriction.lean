import OAI.AlgebraicGeometry.CycleClass.Thom.Local.CompactStage

/-! # Compact Stage Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CompactStageRestriction.Constructions.HigherThom

noncomputable section

/-! The original global compact stage and its local stage form the actual relative restriction square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceCompactThomStageIso_open_restriction
    (U : Opens Z.regularAmbientSpace)
    (K : Compacts ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) (q : ℕ) :
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U))
      ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K q).hom ≫
        (Local.CompactStage.Constructions.HigherThom.regularSourceLocalCompactThomStageIso Z U a ha K q).hom =
      (Regular.CompactStage.Constructions.HigherThom.regularSourceCompactThomStageIso Z a ha (Local.CompactStage.Constructions.HigherThom.regularLocalCompactSourceImage Z U K) q).hom ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
          (Local.CompactStage.Constructions.HigherThom.regularLocalCompactTarget_mapsTo Z U K) ((2 * p)+q) := by
  rw [HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom]
  let L := Local.CompactStage.Constructions.HigherThom.regularLocalCompactSourceImage Z U K
  let O := Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z L
  exact Supported.SourceNaturality.Constructions.HigherThom.sourceTargetIso_naturality
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAnalyticSpace) S q) (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement_preimage Z L)))
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) S q)
      (Local.CompactStage.Constructions.HigherThom.regularLocalCompactSourceComplement Z U K)))
    (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha O q)
    (Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha O U q)
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) S ((2 * p)+q)) (Regular.CompactStage.Constructions.HigherThom.regularCompactThom_unionComplement Z L)))
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of U) S ((2 * p)+q)) (Local.CompactStage.Constructions.HigherThom.regularLocalCompactTargetComplement Z U K))) _ _ _ _
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U))
      (Local.CompactStage.Constructions.HigherThom.regularLocalCompactSourceComplement Z U K) (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement_preimage Z L)
      (fun _ hx => hx)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement
        (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U))
        ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K) q)
    (GlobalSourceOpenNaturality.Constructions.HigherThom.regularSourceThomSupportedGlobalIso_open_naturality Z a ha O U q)
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
      (Local.CompactStage.Constructions.HigherThom.regularLocalCompactTargetComplement Z U K) (Regular.CompactStage.Constructions.HigherThom.regularCompactThom_unionComplement Z L)
      (fun _ hx => hx) (Local.CompactStage.Constructions.HigherThom.regularLocalCompactTarget_mapsTo Z U K) ((2 * p)+q))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CompactStageRestriction.Constructions.HigherThom
