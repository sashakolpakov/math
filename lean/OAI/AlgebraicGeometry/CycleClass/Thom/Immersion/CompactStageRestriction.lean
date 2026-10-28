import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceOpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction

/-! # Compact Stage Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactStageRestriction.Constructions.Construction

noncomputable section

section

/-! The global construction restricted to an exact compact source support inside any open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (U : Opens Z.regularAmbientSpace)

abbrev regularLocalCompactSourceImage (K : Compacts ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) :=
  HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace)
    ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) K

theorem regularLocalCompactSourceComplement (K : Compacts ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj
        (SupportedThomSource.Constructions.Construction.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K)) :
          Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
      ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U) =
        (K : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))ᶜ := by
  rw [SupportedThomSource.Constructions.Construction.regularCompactImageComplement_preimage]
  exact HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions.compactImage_openInclusion_complement
    (X := TopCat.of Z.regularAnalyticSpace) ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U) K

theorem regularLocalCompactTargetComplement (K : Compacts ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ SupportedThomSource.Constructions.Construction.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K) :
        Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U =
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) K : Set U)ᶜ := by
  rw [SupportedThomSource.Constructions.Construction.regularCompactThom_unionComplement]
  exact HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions.compactImage_openPreimage_complement (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U K

theorem regularLocalCompactTarget_mapsTo (K : Compacts ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) :
    Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) K : Set U)ᶜ
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) (regularLocalCompactSourceImage Z U K) :
        Set Z.regularAmbientSpace)ᶜ := by
  intro y hy
  exact (Set.ext_iff.mp
    (HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions.compactImage_openPreimage_complement (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U K) y).mpr hy

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceLocalCompactThomStageIso
    (K : Compacts ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
      (K : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) K : Set U)ᶜ ((2 * p)+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) S q)
      (regularLocalCompactSourceComplement Z U K))).symm ≪≫
    SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha
      (SupportedThomSource.Constructions.Construction.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K)) U q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S ((2 * p)+q))
      (regularLocalCompactTargetComplement Z U K))

end

/-! The original global compact stage and its local stage form the actual relative restriction square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceCompactThomStageIso_open_restriction
    (U : Opens Z.regularAmbientSpace)
    (K : Compacts ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) (q : ℕ) :
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
      ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K q).hom ≫
        (regularSourceLocalCompactThomStageIso Z U a ha K q).hom =
      (SupportedThomSource.Constructions.Construction.regularSourceCompactThomStageIso Z a ha (regularLocalCompactSourceImage Z U K) q).hom ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
          (regularLocalCompactTarget_mapsTo Z U K) ((2 * p)+q) := by
  rw [HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom]
  let L := regularLocalCompactSourceImage Z U K
  let O := SupportedThomSource.Constructions.Construction.regularCompactImageComplement Z L
  exact SupportedSourceNaturality.Constructions.Construction.sourceTargetIso_naturality
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAnalyticSpace) S q) (SupportedThomSource.Constructions.Construction.regularCompactImageComplement_preimage Z L)))
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) S q)
      (regularLocalCompactSourceComplement Z U K)))
    (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha O q)
    (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha O U q)
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) S ((2 * p)+q)) (SupportedThomSource.Constructions.Construction.regularCompactThom_unionComplement Z L)))
    (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of U) S ((2 * p)+q)) (regularLocalCompactTargetComplement Z U K))) _ _ _ _
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
      (regularLocalCompactSourceComplement Z U K) (SupportedThomSource.Constructions.Construction.regularCompactImageComplement_preimage Z L)
      (fun _ hx => hx)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement
        (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace) ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
        ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U).isOpen.isOpenEmbedding_subtypeVal K) q)
    (GlobalSourceOpenNaturality.Constructions.Construction.regularSourceThomSupportedGlobalIso_open_naturality Z a ha O U q)
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
      (regularLocalCompactTargetComplement Z U K) (SupportedThomSource.Constructions.Construction.regularCompactThom_unionComplement Z L)
      (fun _ hx => hx) (regularLocalCompactTarget_mapsTo Z U K) ((2 * p)+q))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactStageRestriction.Constructions.Construction
