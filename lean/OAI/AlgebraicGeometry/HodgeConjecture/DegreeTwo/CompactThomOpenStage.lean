import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomStageRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomZero
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenCompactStageDescent

/-! # Compact Thom Open Stage -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomOpenStage.Constructions

noncomputable section

/-! The global compact Thom pushforward on a class extended from any open source neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceCompactThomPushforward_open_stage (U : Opens Z.regularAmbientSpace)
    (K : Compacts ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) K q ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAnalyticSpace)
        ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U) q ≫
      CompactThomZero.Constructions.regularSourceCompactThomPushforward Z a ha q =
    (CompactThomStageRestriction.Constructions.regularSourceLocalCompactThomStageIso Z U a ha K q).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (OpenEmbeddingExtension.Constructions.embeddingCompactImage (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) K) (2+q) ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of Z.regularAmbientSpace) U (2+q) := by
  let L := CompactThomStageRestriction.Constructions.regularLocalCompactSourceImage Z U K
  let T := OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) L
  let R := OpenEmbeddingExtension.Constructions.embeddingCompactImage (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) K
  let e := OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
    ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K q
  rw [← Category.assoc (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) K q)]
  apply OpenCompactStageDescent.Constructions.compactStageSquare_desc e _
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) L q)
    (RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso Z a ha L q).hom
    (CompactThomStageRestriction.Constructions.regularSourceLocalCompactThomStageIso Z U a ha K q).hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U) (CompactThomStageRestriction.Constructions.regularLocalCompactTarget_mapsTo Z U K) (2+q)) _
    (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) T (2+q)) _
  · dsimp only [e]
    rw [OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom, ← OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace]
    exact OpenCompactStageDescent.Constructions.relativePullback_compactOpenExtension
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
      ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K L rfl
      (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
        ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K) q
  · exact CompactThomStageRestriction.Constructions.regularSourceCompactThomStageIso_open_restriction Z a ha U K q
  · rw [← OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace]
    exact OpenCompactStageDescent.Constructions.relativePullback_compactOpenExtension
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U) U.isOpen.isOpenEmbedding_subtypeVal R T
      (congrArg (fun W : Compacts Z.regularAmbientSpace => (W : Set Z.regularAmbientSpace))
        (CompactImageOpenRestriction.Constructions.compactImage_openPreimage_square (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U K).symm)
      (CompactThomStageRestriction.Constructions.regularLocalCompactTarget_mapsTo Z U K) (2+q)
  · exact CompactThomZero.Constructions.regularSourceCompactThomPushforward_stage Z a ha q L

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomOpenStage.Constructions
