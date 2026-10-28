import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CompactThomCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpen

/-! # Compact Thom Restriction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CompactThomRestriction

noncomputable section

section

/-! The native global supported Thom isomorphism restricts to the actual relative isomorphism on every open neighborhood. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpen.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem relativeCohomologyPresheafTopIso_restrict (X : TopCat.{0}) (A : Set X) (U : Opens X) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X A n).hom ≫
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X A U n =
    HomologicalComplex.homologyMap ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X A).map
      (homOfLE (show U ≤ ⊤ from le_top)).op) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
  rw [← HomologicalComplex.homologyMap_comp]
  congr 1
  dsimp only [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso]
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp]
  rfl

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_restrict
    (O U : Opens D.regularAmbientSpace) (n : ℕ) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAnalyticSpace)
      (((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj O) : Set D.regularAnalyticSpace)
      ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U) n ≫
      (HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso D a ha O U n).hom =
    (HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso D a ha O n).hom ≫
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        ((D.regularThomComplementOpen ⊔ O : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace) U (2+n) := by
  have hn := HodgeConjecture.DegreeTwo.SourceThomOpen.Constructions.regularSourceThomSupportedRelativeIso_open_naturality D a ha O
    (homOfLE (show U ≤ ⊤ from le_top)) n
  unfold HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [relativeCohomologyPresheafTopIso_restrict]
  apply (cancel_epi (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ)
    (TopCat.of D.regularAnalyticSpace)
    (((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj O) : Set D.regularAnalyticSpace) n).hom).1
  rw [← Category.assoc, relativeCohomologyPresheafTopIso_restrict, Iso.hom_inv_id_assoc]
  exact hn

end

/-! The native compact Thom stages retain their original maps when restricted to any open neighborhood. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpen.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem relativeCohomologyOpenRestriction_supportCongr (X : TopCat.{0}) {A B : Set X}
    (e : A = B) (U : Opens X) (n : ℕ) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X A U n ≫
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of U)
        (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) S U) e) n).hom =
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X e n).hom ≫
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) X B U n := by
  subst B
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

def regularCompactThomRestrictedStageIso (U : Opens D.regularAmbientSpace)
    (K : Compacts D.regularAnalyticSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
        (K : Set D.regularAnalyticSpace)ᶜ ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U)) n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
        (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) K : Set D.regularAmbientSpace)ᶜ U) (2+n) :=
  (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr
    (TopCat.of ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U))
    (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace) S
      ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U)) (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage D K)) n).symm ≪≫
  HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso D a ha (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D K) U n ≪≫
  AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of U)
    (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace) S U)
      (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactThom_unionComplement D K)) (2+n)

theorem regularSourceCompactThomStageIso_restrict (U : Opens D.regularAmbientSpace)
    (K : Compacts D.regularAnalyticSpace) (n : ℕ) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAnalyticSpace)
      (K : Set D.regularAnalyticSpace)ᶜ ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U) n ≫
      (regularCompactThomRestrictedStageIso D a ha U K n).hom =
    (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso D a ha K n).hom ≫
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) K : Set D.regularAmbientSpace)ᶜ U (2+n) := by
  exact HodgeConjecture.DegreeTwo.SupportedSourceThomNaturality.Constructions.sourceTargetIso_naturality
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAnalyticSpace)
      (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage D K) n)
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr
      (TopCat.of ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U))
      (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace) S
        ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U)) (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage D K)) n)
    (HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso D a ha (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D K) n)
    (HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso D a ha (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D K) U n)
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
      (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactThom_unionComplement D K) (2+n))
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of U)
      (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace) S U)
        (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactThom_unionComplement D K)) (2+n)) _ _ _ _
    (relativeCohomologyOpenRestriction_supportCongr (TopCat.of D.regularAnalyticSpace)
      (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage D K) ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U) n)
    (regularSourceThomSupportedGlobalIso_restrict D a ha (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement D K) U n)
    (relativeCohomologyOpenRestriction_supportCongr (TopCat.of D.regularAmbientSpace)
      (HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactThom_unionComplement D K) U (2+n))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CompactThomRestriction
