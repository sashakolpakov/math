import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSourceOpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.CompactStage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction

/-! # Compact Stage -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.CompactStage.Constructions.HigherThom

noncomputable section

/-! The global construction restricted to an exact compact source support inside any open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (U : Opens Z.regularAmbientSpace)

abbrev regularLocalCompactSourceImage (K : Compacts ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) :=
  HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAnalyticSpace)
    ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) K

theorem regularLocalCompactSourceComplement (K : Compacts ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj
        (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K)) :
          Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
      ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U) =
        (K : Set ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U))ᶜ := by
  rw [Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement_preimage]
  exact HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions.compactImage_openInclusion_complement
    (X := TopCat.of Z.regularAnalyticSpace) ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U) K

theorem regularLocalCompactTargetComplement (K : Compacts ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K) :
        Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U =
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) U) K : Set U)ᶜ := by
  rw [Regular.CompactStage.Constructions.HigherThom.regularCompactThom_unionComplement]
  exact HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions.compactImage_openPreimage_complement (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) U K

theorem regularLocalCompactTarget_mapsTo (K : Compacts ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) :
    Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of Z.regularAmbientSpace) U)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) U) K : Set U)ᶜ
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) (regularLocalCompactSourceImage Z U K) :
        Set Z.regularAmbientSpace)ᶜ := by
  intro y hy
  exact (Set.ext_iff.mp
    (HodgeConjecture.DegreeTwo.CompactImageOpenRestriction.Constructions.compactImage_openPreimage_complement (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) U K) y).mpr hy

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceLocalCompactThomStageIso
    (K : Compacts ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U))
      (K : Set ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U))ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) U) K : Set U)ᶜ ((2 * p)+q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U)) S q)
      (regularLocalCompactSourceComplement Z U K))).symm ≪≫
    Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha
      (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z (regularLocalCompactSourceImage Z U K)) U q ≪≫
    eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) S ((2 * p)+q))
      (regularLocalCompactTargetComplement Z U K))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.CompactStage.Constructions.HigherThom
