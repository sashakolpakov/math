import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactStageRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SourceCompactPushforward
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenCompactStageDescent

/-! # Compact Open Stage -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactOpenStage.Constructions.Construction

noncomputable section

/-! The global compact Thom pushforward on a class extended from any open source neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenCompactStageDescent.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceCompactThomPushforward_open_stage (U : Opens Z.regularAmbientSpace)
    (K : Compacts ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) K q ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAnalyticSpace)
        ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U) q ≫
      SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward Z a ha q =
    (CompactStageRestriction.Constructions.Construction.regularSourceLocalCompactThomStageIso Z U a ha K q).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) K) ((2 * p)+q) ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAmbientSpace) U ((2 * p)+q) := by
  let L := CompactStageRestriction.Constructions.Construction.regularLocalCompactSourceImage Z U K
  let T := HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) L
  let R := HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) K
  let e := HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
    ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K q
  rw [← Category.assoc (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) K q)]
  apply HodgeConjecture.DegreeTwo.OpenCompactStageDescent.Constructions.compactStageSquare_desc e _
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) L q)
    (SupportedThomSource.Constructions.Construction.regularSourceCompactThomStageIso Z a ha L q).hom
    (CompactStageRestriction.Constructions.Construction.regularSourceLocalCompactThomStageIso Z U a ha K q).hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U) (CompactStageRestriction.Constructions.Construction.regularLocalCompactTarget_mapsTo Z U K) ((2 * p)+q)) _
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) T ((2 * p)+q)) _
  · dsimp only [e]
    rw [HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom, ← HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace]
    exact HodgeConjecture.DegreeTwo.OpenCompactStageDescent.Constructions.relativePullback_compactOpenExtension
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
      ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K L rfl
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement
        (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
        ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K) q
  · exact CompactStageRestriction.Constructions.Construction.regularSourceCompactThomStageIso_open_restriction Z a ha U K q
  · rw [← HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace]
    exact HodgeConjecture.DegreeTwo.OpenCompactStageDescent.Constructions.relativePullback_compactOpenExtension
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U) U.isOpen.isOpenEmbedding_subtypeVal R T
      (congrArg (fun W : Compacts Z.regularAmbientSpace => (W : Set Z.regularAmbientSpace))
        (HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions.compactImage_openPreimage_square (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U K).symm)
      (CompactStageRestriction.Constructions.Construction.regularLocalCompactTarget_mapsTo Z U K) ((2 * p)+q)
  · exact SourceCompactPushforward.Constructions.Construction.regularSourceCompactThomPushforward_stage Z a ha q L

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactOpenStage.Constructions.Construction
