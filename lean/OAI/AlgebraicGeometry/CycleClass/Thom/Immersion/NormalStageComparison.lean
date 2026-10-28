import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.LocalSupportEquality
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactStageRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RegularNormalComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition

/-! # Normal Stage Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.NormalStageComparison

noncomputable section

section

/-! Literal support identities for extending a normal-chart compact Thom stage into the global ambient space. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.Construction

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p) (x : D.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D.regularAnalyticModel (Fin p → ℂ) D.regularComplementInclusion x)

def regularNormalGlobalSourceCompact (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) :
    Compacts D.regularAnalyticSpace :=
  HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAnalyticSpace)
    (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P : Set D.regularAnalyticSpace)) K

theorem regularNormalCompactImage_square (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) :
    HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V D) (regularNormalGlobalSourceCompact D x P K) =
    HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) (P.openNeighborhood : Set D.regularAmbientSpace))
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) := by
  unfold regularNormalGlobalSourceCompact
  rw [HodgeConjecture.DegreeTwo.OpenExtensionComposition.Constructions.embeddingCompactImage_comp, HodgeConjecture.DegreeTwo.OpenExtensionComposition.Constructions.embeddingCompactImage_comp]
  rfl

theorem relativeOpenSubspace_compactImage_complement (X : TopCat.{0}) (U : Opens X) (K : Compacts U) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (Geometric.LocalHomology.Cycles.subspaceInclusion X (U : Set X)) K : Set X)ᶜ U = (K : Set U)ᶜ := by
  change Subtype.val ⁻¹' (Subtype.val '' (K : Set U))ᶜ = _
  rw [Set.preimage_compl, Set.preimage_image_eq _ Subtype.val_injective]

theorem regularNormalGlobalSourceComplement (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V D)).obj
        (SupportedThomSource.Constructions.Construction.regularCompactImageComplement D (regularNormalGlobalSourceCompact D x P K))) : Set D.regularAnalyticSpace)
      (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P) = (K : Set (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P))ᶜ := by
  rw [SupportedThomSource.Constructions.Construction.regularCompactImageComplement_preimage]
  exact relativeOpenSubspace_compactImage_complement (TopCat.of D.regularAnalyticSpace)
    (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P) K

theorem regularNormalGlobalTargetComplement (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      ((D.regularThomComplementOpen ⊔ SupportedThomSource.Constructions.Construction.regularCompactImageComplement D
        (regularNormalGlobalSourceCompact D x P K) : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace)
      P.openNeighborhood =
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K :
      Set P.neighborhood)ᶜ := by
  rw [SupportedThomSource.Constructions.Construction.regularCompactThom_unionComplement, regularNormalCompactImage_square]
  exact relativeOpenSubspace_compactImage_complement (TopCat.of D.regularAmbientSpace)
    P.openNeighborhood _

def regularNormalCylinderAmbientComplement (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) :
    Opens D.regularAmbientSpace :=
  HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of D.regularAmbientSpace) P.openNeighborhood
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K)

theorem regularNormalCylinderSourceComplement (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V D)).obj
        (regularNormalCylinderAmbientComplement D x P K)) : Set D.regularAnalyticSpace)
      (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P) = (K : Set (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P))ᶜ := by
  exact (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of D.regularAmbientSpace) P.openNeighborhood
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K)
    (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V D)).trans
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplement_source P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K)

theorem regularNormalCylinderTargetComplement (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      ((D.regularThomComplementOpen ⊔ regularNormalCylinderAmbientComplement D x P K : Opens D.regularAmbientSpace) :
        Set D.regularAmbientSpace) P.openNeighborhood =
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K :
      Set P.neighborhood)ᶜ := by
  rw [regularNormalCylinderAmbientComplement, HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_union]
  exact HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetraction_union_complement P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K

theorem regularNormalCylinder_le_globalComplement (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) :
    regularNormalCylinderAmbientComplement D x P K ≤
      SupportedThomSource.Constructions.Construction.regularCompactImageComplement D (regularNormalGlobalSourceCompact D x P K) := by
  intro y hy
  change y ∈ Subtype.val '' (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P
    D.isClosedEmbedding_regularComplementInclusion.isEmbedding K : Set P.neighborhood) at hy
  obtain ⟨z, hz, rfl⟩ := hy
  change z ∈ AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V D) (regularNormalGlobalSourceCompact D x P K) :
      Set D.regularAmbientSpace)ᶜ P.openNeighborhood
  rw [regularNormalCompactImage_square, relativeOpenSubspace_compactImage_complement,
    ← HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetraction_union_complement P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K]
  exact Or.inr hz

end Constructions.Construction

end

/-! The actual local normal Thom stage equals the restriction of the native global stage at the same compact source image. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.Construction

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (D : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = D.regularThomClass)
variable (x : D.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D.regularAnalyticModel (Fin p → ℂ) D.regularComplementInclusion x)

def regularNormalGlobalThomStageIsoOnOpen (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P))
      (K : Set (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P))ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P
        D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K : Set P.neighborhood)ᶜ ((2 * p)+q) :=
  (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P))
    (regularNormalGlobalSourceComplement D x P K) q).symm ≪≫
  SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso D a ha
    (SupportedThomSource.Constructions.Construction.regularCompactImageComplement D (regularNormalGlobalSourceCompact D x P K)) P.openNeighborhood q ≪≫
  AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of P.neighborhood)
    (regularNormalGlobalTargetComplement D x P K) ((2 * p)+q)

theorem regularNormalSourceThomStageIso_eq_global (K : Compacts (RegularNormalStage.Constructions.Construction.regularNormalSourceOpen D x P)) (q : ℕ) :
    RegularNormalStage.Constructions.Construction.regularNormalSourceThomStageIso D a ha x P K q = regularNormalGlobalThomStageIsoOnOpen D a ha x P K q := by
  have hs := (regularNormalGlobalSourceComplement D x P K).trans
    (regularNormalCylinderSourceComplement D x P K).symm
  have ht := (regularNormalGlobalTargetComplement D x P K).trans
    (regularNormalCylinderTargetComplement D x P K).symm
  have hn := LocalSupportEquality.Constructions.Construction.regularSourceThomSupportedRelativeIso_supportEquality D a ha
    (regularNormalCylinder_le_globalComplement D x P K) P.openNeighborhood hs ht q
  unfold RegularNormalStage.Constructions.Construction.regularNormalSourceThomStageIso LocalSupportCup.Constructions.Construction.regularSourceThomLocalSupportIso
  erw [hn]
  apply Iso.ext
  simp only [regularNormalGlobalThomStageIsoOnOpen, Iso.trans_hom, Iso.symm_hom,
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end Constructions.Construction

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.NormalStageComparison
