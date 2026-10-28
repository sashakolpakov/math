import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpenNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactThomStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction

/-! # Compact Thom Stage Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomStageRestriction.Constructions

noncomputable section

section

/-! The global construction restricted to an exact compact source support inside any open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (U : Opens Z.regularAmbientSpace)

abbrev regularLocalCompactSourceImage (K : Compacts ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) :=
  OpenEmbeddingExtension.Constructions.embeddingCompactImage (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace)
    ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) K

theorem regularLocalCompactSourceComplement (K : Compacts ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj
        (RegularCompactThomStage.Constructions.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K)) :
          Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
      ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U) =
        (K : Set ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))ᶜ := by
  rw [RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage]
  exact CompactImageOpenRestriction.Constructions.compactImage_openInclusion_complement
    (X := TopCat.of Z.regularAnalyticSpace) ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U) K

theorem regularLocalCompactTargetComplement (K : Compacts ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ RegularCompactThomStage.Constructions.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K) :
        Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U =
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) K : Set U)ᶜ := by
  rw [RegularCompactThomStage.Constructions.regularCompactThom_unionComplement]
  exact CompactImageOpenRestriction.Constructions.compactImage_openPreimage_complement (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U K

theorem regularLocalCompactTarget_mapsTo (K : Compacts ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) :
    Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) K : Set U)ᶜ
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) (regularLocalCompactSourceImage Z U K) :
        Set Z.regularAmbientSpace)ᶜ := by
  intro y hy
  exact (Set.ext_iff.mp
    (CompactImageOpenRestriction.Constructions.compactImage_openPreimage_complement (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U K) y).mpr hy

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceLocalCompactThomStageIso
    (K : Compacts ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
      (K : Set ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) K : Set U)ᶜ (2+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) S q)
      (regularLocalCompactSourceComplement Z U K))).symm ≪≫
    SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha
      (RegularCompactThomStage.Constructions.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K)) U q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S (2+q))
      (regularLocalCompactTargetComplement Z U K))

end

/-! The original global compact stage and its local stage form the actual relative restriction square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceCompactThomStageIso_open_restriction
    (U : Opens Z.regularAmbientSpace)
    (K : Compacts ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) (q : ℕ) :
    (OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
      ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K q).hom ≫
        (regularSourceLocalCompactThomStageIso Z U a ha K q).hom =
      (RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso Z a ha (regularLocalCompactSourceImage Z U K) q).hom ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
          (regularLocalCompactTarget_mapsTo Z U K) (2+q) := by
  rw [OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom]
  let L := regularLocalCompactSourceImage Z U K
  let O := RegularCompactThomStage.Constructions.regularCompactImageComplement Z L
  exact SupportedSourceThomNaturality.Constructions.sourceTargetIso_naturality
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAnalyticSpace) S q) (RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage Z L)))
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U)) S q)
      (regularLocalCompactSourceComplement Z U K)))
    (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha O q)
    (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U q)
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) S (2+q)) (RegularCompactThomStage.Constructions.regularCompactThom_unionComplement Z L)))
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of U) S (2+q)) (regularLocalCompactTargetComplement Z U K))) _ _ _ _
    (NormalSupportRelative.Constructions.relativePairMap_supportEquality
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
      (regularLocalCompactSourceComplement Z U K) (RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage Z L)
      (fun _ hx => hx)
      (OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))
        ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K) q)
    (SourceThomOpenNaturality.Constructions.regularSourceThomSupportedGlobalIso_open_naturality Z a ha O U q)
    (NormalSupportRelative.Constructions.relativePairMap_supportEquality (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
      (regularLocalCompactTargetComplement Z U K) (RegularCompactThomStage.Constructions.regularCompactThom_unionComplement Z L)
      (fun _ hx => hx) (regularLocalCompactTarget_mapsTo Z U K) (2+q))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomStageRestriction.Constructions
