import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalThomSupportEquality
import OAI.AlgebraicGeometry.DivisorClass.Chern.CompactThomRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularNormalThomComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenEmbeddingExtension

/-! # Normal Thom Stage -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.NormalThomStage

noncomputable section

section

/-! Literal support identities for extending a normal-chart compact Thom stage into the global ambient space. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : D.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D.regularAnalyticModel (Fin 1 → ℂ) D.regularComplementInclusion x)

def regularNormalGlobalSourceCompact (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    Compacts D.regularAnalyticSpace :=
  HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAnalyticSpace)
    (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P : Set D.regularAnalyticSpace)) K

theorem regularNormalCompactImage_square (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) (regularNormalGlobalSourceCompact D x P K) =
    HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) (P.openNeighborhood : Set D.regularAmbientSpace))
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) := by
  unfold regularNormalGlobalSourceCompact
  rw [HodgeConjecture.DegreeTwo.OpenExtensionComposition.Constructions.embeddingCompactImage_comp, HodgeConjecture.DegreeTwo.OpenExtensionComposition.Constructions.embeddingCompactImage_comp]
  rfl

theorem relativeOpenSubspace_compactImage_complement (X : TopCat.{0}) (U : Opens X) (K : Compacts U) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U : Set X)) K : Set X)ᶜ U = (K : Set U)ᶜ := by
  change Subtype.val ⁻¹' (Subtype.val '' (K : Set U))ᶜ = _
  rw [Set.preimage_compl, Set.preimage_image_eq _ Subtype.val_injective]

theorem regularNormalGlobalSourceComplement (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
      (((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj
        (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D (regularNormalGlobalSourceCompact D x P K))) : Set D.regularAnalyticSpace)
      (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P) = (K : Set (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P))ᶜ := by
  rw [HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage]
  exact relativeOpenSubspace_compactImage_complement (TopCat.of D.regularAnalyticSpace)
    (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P) K

theorem regularNormalGlobalTargetComplement (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      ((D.regularThomComplementOpen ⊔ HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D
        (regularNormalGlobalSourceCompact D x P K) : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace)
      P.openNeighborhood =
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K :
      Set P.neighborhood)ᶜ := by
  rw [HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactThom_unionComplement, regularNormalCompactImage_square]
  exact relativeOpenSubspace_compactImage_complement (TopCat.of D.regularAmbientSpace)
    P.openNeighborhood _

def regularNormalCylinderAmbientComplement (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    Opens D.regularAmbientSpace :=
  HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen (X := TopCat.of D.regularAmbientSpace) P.openNeighborhood
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K)

theorem regularNormalCylinderSourceComplement (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
      (((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj
        (regularNormalCylinderAmbientComplement D x P K)) : Set D.regularAnalyticSpace)
      (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P) = (K : Set (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P))ᶜ := by
  exact (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := TopCat.of D.regularAmbientSpace) P.openNeighborhood
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K)
    (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).trans
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplement_source P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K)

theorem regularNormalCylinderTargetComplement (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      ((D.regularThomComplementOpen ⊔ regularNormalCylinderAmbientComplement D x P K : Opens D.regularAmbientSpace) :
        Set D.regularAmbientSpace) P.openNeighborhood =
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K :
      Set P.neighborhood)ᶜ := by
  rw [regularNormalCylinderAmbientComplement, HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_union]
  exact HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetraction_union_complement P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K

theorem regularNormalCylinder_le_globalComplement (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    regularNormalCylinderAmbientComplement D x P K ≤
      HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D (regularNormalGlobalSourceCompact D x P K) := by
  intro y hy
  change y ∈ Subtype.val '' (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetractionComplementOpen P
    D.isClosedEmbedding_regularComplementInclusion.isEmbedding K : Set P.neighborhood) at hy
  obtain ⟨z, hz, rfl⟩ := hy
  change z ∈ AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) (regularNormalGlobalSourceCompact D x P K) :
      Set D.regularAmbientSpace)ᶜ P.openNeighborhood
  rw [regularNormalCompactImage_square, relativeOpenSubspace_compactImage_complement,
    ← HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairRetraction_union_complement P D.isClosedEmbedding_regularComplementInclusion.isEmbedding K]
  exact Or.inr hz

end

section

/-! The actual local normal Thom stage equals the restriction of the native global stage at the same compact source image. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)
variable (x : D.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D.regularAnalyticModel (Fin 1 → ℂ) D.regularComplementInclusion x)

def regularNormalGlobalThomStageIsoOnOpen (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P))
      (K : Set (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P))ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P
        D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K : Set P.neighborhood)ᶜ (2+q) :=
  (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P))
    (regularNormalGlobalSourceComplement D x P K) q).symm ≪≫
  HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso D a ha
    (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D (regularNormalGlobalSourceCompact D x P K)) P.openNeighborhood q ≪≫
  AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of P.neighborhood)
    (regularNormalGlobalTargetComplement D x P K) (2+q)

theorem regularNormalSourceThomStageIso_eq_global (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) (q : ℕ) :
    HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso D a ha x P K q = regularNormalGlobalThomStageIsoOnOpen D a ha x P K q := by
  have hs := (regularNormalGlobalSourceComplement D x P K).trans
    (regularNormalCylinderSourceComplement D x P K).symm
  have ht := (regularNormalGlobalTargetComplement D x P K).trans
    (regularNormalCylinderTargetComplement D x P K).symm
  have hn := LocalThomSupportEquality.regularSourceThomSupportedRelativeIso_supportEquality D a ha
    (regularNormalCylinder_le_globalComplement D x P K) P.openNeighborhood hs ht q
  unfold HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso HodgeConjecture.DegreeTwo.LocalSupportCup.Constructions.regularSourceThomLocalSupportIso
  erw [hn]
  apply Iso.ext
  simp only [regularNormalGlobalThomStageIsoOnOpen, Iso.trans_hom, Iso.symm_hom,
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end

section

/-! The original global compact Thom stage and the normal-chart stage commute with actual pair restriction. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : D.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D.regularAnalyticModel (Fin 1 → ℂ) D.regularComplementInclusion x)

theorem regularNormalAmbientComplementMapsTo (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) :
    Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) (P.openNeighborhood : Set D.regularAmbientSpace))
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K :
        Set P.neighborhood)ᶜ
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) (regularNormalGlobalSourceCompact D x P K) :
        Set D.regularAmbientSpace)ᶜ := by
  intro z hz
  change z.val ∉ (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) (regularNormalGlobalSourceCompact D x P K) :
    Set D.regularAmbientSpace)
  rw [regularNormalCompactImage_square]
  rintro ⟨w, hw, he⟩
  exact hz ((Subtype.ext he : w = z) ▸ hw)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceCompactThomStageIso_normal_restrict
    (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) (q : ℕ) :
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAnalyticSpace) (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P : Set D.regularAnalyticSpace))
      (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P).isOpen.isOpenEmbedding_subtypeVal K q).hom ≫
      (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso D a ha x P K q).hom =
    (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso D a ha (regularNormalGlobalSourceCompact D x P K) q).hom ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) (P.openNeighborhood : Set D.regularAmbientSpace))
        (regularNormalAmbientComplementMapsTo D x P K) (2+q) := by
  rw [regularNormalSourceThomStageIso_eq_global]
  let G := regularNormalGlobalSourceCompact D x P K
  let U := P.openNeighborhood
  let S := HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P
  let O := HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D G
  exact HodgeConjecture.DegreeTwo.SupportedSourceThomNaturality.Constructions.sourceTargetIso_naturality
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAnalyticSpace) (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage D G) q)
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of S) (regularNormalGlobalSourceComplement D x P K) q)
    (HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso D a ha O q)
    (HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso D a ha O U q)
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace) (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactThom_unionComplement D G) (2+q))
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of U) (regularNormalGlobalTargetComplement D x P K) (2+q)) _ _ _ _
    (by
      rw [HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom]
      exact HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAnalyticSpace) (S : Set D.regularAnalyticSpace))
        (regularNormalGlobalSourceComplement D x P K) (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage D G)
        (fun _ hx => hx) (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement
          (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAnalyticSpace) (S : Set D.regularAnalyticSpace))
          S.isOpen.isOpenEmbedding_subtypeVal K) q)
    (CompactThomRestriction.regularSourceThomSupportedGlobalIso_restrict D a ha O U q)
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) (U : Set D.regularAmbientSpace))
      (regularNormalGlobalTargetComplement D x P K) (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactThom_unionComplement D G)
      (fun _ hx => hx) (regularNormalAmbientComplementMapsTo D x P K) (2+q))

end

section

/-! Actual excision transports the native global Thom stage to its original normal-chart stage. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : D.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D.regularAnalyticModel (Fin 1 → ℂ) D.regularComplementInclusion x)

def regularNormalAmbientExcisionIso (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) (regularNormalGlobalSourceCompact D x P K) :
        Set D.regularAmbientSpace)ᶜ q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K :
        Set P.neighborhood)ᶜ q :=
  AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
    (congrArg (fun J : Compacts D.regularAmbientSpace => (J : Set D.regularAmbientSpace)ᶜ)
      (regularNormalCompactImage_square D x P K)) q ≪≫
  HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) P.openNeighborhood)
    P.openNeighborhood.isOpen.isOpenEmbedding_subtypeVal
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) q

theorem regularNormalAmbientExcisionIso_hom (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) (q : ℕ) :
    (regularNormalAmbientExcisionIso D x P K q).hom =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) P.openNeighborhood)
      (regularNormalAmbientComplementMapsTo D x P K) q := by
  unfold regularNormalAmbientExcisionIso
  rw [Iso.trans_hom, HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso_hom]
  have h := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.relativePairMap_supportEquality
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) P.openNeighborhood) rfl
    (congrArg (fun J : Compacts D.regularAmbientSpace => (J : Set D.regularAmbientSpace)ᶜ)
      (regularNormalCompactImage_square D x P K))
    (regularNormalAmbientComplementMapsTo D x P K)
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbedding_mapsTo_image_complement
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) P.openNeighborhood)
      P.openNeighborhood.isOpen.isOpenEmbedding_subtypeVal
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K : Set P.neighborhood)) q
  simpa only [eqToIso_refl, Iso.refl_hom, Category.comp_id, AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr] using h.symm

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceCompactThomStageIso_normal_excision
    (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) (q : ℕ) :
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactStageIso
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAnalyticSpace) (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P : Set D.regularAnalyticSpace))
      (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P).isOpen.isOpenEmbedding_subtypeVal K q).inv ≫
      (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso D a ha (regularNormalGlobalSourceCompact D x P K) q).hom =
    (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso D a ha x P K q).hom ≫
      (regularNormalAmbientExcisionIso D x P K (2+q)).inv := by
  have hn := regularSourceCompactThomStageIso_normal_restrict D x P a ha K q
  rw [← regularNormalAmbientExcisionIso_hom] at hn
  apply (cancel_mono (regularNormalAmbientExcisionIso D x P K (2+q)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [← hn, Iso.inv_hom_id_assoc]

end

/-! Open extension from each normal neighborhood commutes with the actual native compact Thom pushforward. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (x : D.regularAnalyticSpace)
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair D.regularAnalyticModel (Fin 1 → ℂ) D.regularComplementInclusion x)

theorem regularNormalAmbientExcisionIso_inv_ι (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) (q : ℕ) :
    (regularNormalAmbientExcisionIso D x P K q).inv ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) (regularNormalGlobalSourceCompact D x P K)) q =
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) q ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAmbientSpace) P.openNeighborhood q := by
  have hc := Intrinsic.CompactThomCup.relativeCohomologyCongr_compactι (TopCat.of D.regularAmbientSpace)
    (regularNormalCompactImage_square D x P K).symm q
  change (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
    (congrArg (fun J : Compacts D.regularAmbientSpace => (J : Set D.regularAmbientSpace)ᶜ)
      (regularNormalCompactImage_square D x P K)) q).inv ≫ _ = _ at hc
  simp only [regularNormalAmbientExcisionIso, Iso.trans_inv, Category.assoc]
  rw [hc, ← HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.compactSupportCohomologyι_embeddingExtension, HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace]
  rfl

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceCompactThomPushforward_normal_stage (K : Compacts (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) (q : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P)) K q ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAnalyticSpace) (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P) q ≫
      HodgeConjecture.DegreeTwo.CompactThomZero.Constructions.regularSourceCompactThomPushforward D a ha q =
    (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceThomStageIso D a ha x P K q).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
        (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P D.isClosedEmbedding_regularComplementInclusion.isEmbedding) K) (2+q) ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of D.regularAmbientSpace) P.openNeighborhood (2+q) := by
  erw [← HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace (Y := TopCat.of D.regularAnalyticSpace)
    (HodgeConjecture.DegreeTwo.RegularNormalThomStage.Constructions.regularNormalSourceOpen D x P) q,
    ← Category.assoc, HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.compactSupportCohomologyι_embeddingExtension, Category.assoc,
    HodgeConjecture.DegreeTwo.CompactThomZero.Constructions.regularSourceCompactThomPushforward_stage D a ha q (regularNormalGlobalSourceCompact D x P K), ← Category.assoc,
    regularSourceCompactThomStageIso_normal_excision D x P a ha K q, Category.assoc,
    regularNormalAmbientExcisionIso_inv_ι D x P K (2+q)]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.NormalThomStage
