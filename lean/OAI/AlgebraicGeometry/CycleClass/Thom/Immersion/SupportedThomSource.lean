import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedRelative
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.ClosedSupportResolution
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs

/-! # Supported Thom Source -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource.Constructions.Construction

noncomputable section

section

/-! The source–Thom isomorphism with a prescribed closed support, on the original relative groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceThomSupportedRelativeIso (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAnalyticSpace)
        (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) :
          Set Z.regularAnalyticSpace) ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
        ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U)
      ((2 * p)+n) :=
  (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) O U n).symm ≪≫
    ClosedSupportResolution.Constructions.Construction.regularSourceThomClosedSupportIso Z a ha O U n ≪≫ SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso Z O U n

end

section

/-! The actual global source-relative Thom isomorphism, retaining any specified closed support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceThomSupportedGlobalIso (O : Opens Z.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) :
        Set Z.regularAnalyticSpace) n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ((2 * p)+n) :=
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
    (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) :
      Set Z.regularAnalyticSpace) n).symm ≪≫
    regularSourceThomSupportedRelativeIso Z a ha O ⊤ n ≪≫
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) ((2 * p)+n)

end

/-! The global Thom isomorphism at an exact compact source support and its actual ambient image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

def regularCompactImageComplement (K : Compacts Z.regularAnalyticSpace) : Opens Z.regularAmbientSpace :=
  ⟨(HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) K : Set Z.regularAmbientSpace)ᶜ,
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) K).isCompact.isClosed.isOpen_compl⟩

theorem regularCompactImageComplement_preimage (K : Compacts Z.regularAnalyticSpace) :
    (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj (regularCompactImageComplement Z K) :
      Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) = (K : Set Z.regularAnalyticSpace)ᶜ := by
  change (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) ⁻¹'
    ((SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) '' (K : Set Z.regularAnalyticSpace))ᶜ = _
  have hf : Function.Injective (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) :=
    Z.isClosedEmbedding_regularComplementInclusion.injective
  rw [Set.preimage_compl, Set.preimage_image_eq _ hf]

theorem regularThomComplement_le_compactComplement (K : Compacts Z.regularAnalyticSpace) :
    Z.regularThomComplementOpen ≤ regularCompactImageComplement Z K := by
  intro y hy
  change y ∉ Set.range Z.regularComplementInclusion at hy
  change y ∉ (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) '' (K : Set Z.regularAnalyticSpace)
  rintro ⟨x, hx, hxy⟩
  exact hy ⟨x, hxy⟩

theorem regularCompactThom_unionComplement (K : Compacts Z.regularAnalyticSpace) :
    ((Z.regularThomComplementOpen ⊔ regularCompactImageComplement Z K : Opens Z.regularAmbientSpace) :
      Set Z.regularAmbientSpace) =
    (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) K : Set Z.regularAmbientSpace)ᶜ := by
  rw [sup_eq_right.mpr (regularThomComplement_le_compactComplement Z K)]
  rfl

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceCompactThomStageIso (K : Compacts Z.regularAnalyticSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (K : Set Z.regularAnalyticSpace)ᶜ n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) K : Set Z.regularAmbientSpace)ᶜ ((2 * p)+n) :=
  (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAnalyticSpace) B n) (regularCompactImageComplement_preimage Z K))).symm ≪≫
    regularSourceThomSupportedGlobalIso Z a ha (regularCompactImageComplement Z K) n ≪≫
    eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) B ((2 * p)+n)) (regularCompactThom_unionComplement Z K))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource.Constructions.Construction
