import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourcePullback
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupCohomology
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource

/-! # Supported Source Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedSourceCup.Constructions.Construction

noncomputable section

/-! The actual supported source–Thom isomorphism intertwines relative pullback with the original two-support cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourcePullback.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupCohomology.Constructions.Even

set_option backward.isDefEq.respectTransparency false

theorem sourceTargetIso_cup {C : Type*} [Category C] {R S A B X Y : C}
    (u : R ⟶ S) (f : S ⟶ A) (g : S ⟶ B) (eA : A ≅ X) (eAB : A ≅ B) (eB : B ≅ Y)
    (h : R ⟶ X) (cup : R ⟶ Y)
    (hp : u ≫ f ≫ eA.hom = h) (he : f ≫ eAB.hom = g) (hc : u ≫ g ≫ eB.hom = cup) :
    h ≫ (eA.symm ≪≫ eAB ≪≫ eB).hom = cup := by
  rw [← hp]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc f, he]
  exact hc

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_cup (O U : Opens Z.regularAmbientSpace) (q : ℕ) :
    HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.SupportedSourcePullback.Constructions.relativeSourcePullbackMap
      (X := TopCat.of Z.regularAmbientSpace) (Y := TopCat.of Z.regularAnalyticSpace)
      O U (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)) q ≫
        (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha O U q).hom =
      ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace) (O : Set Z.regularAmbientSpace) U)
        (Z.regularThomComplementOpen.isOpen.preimage continuous_subtype_val)
        (O.isOpen.preimage continuous_subtype_val) (2 * p) q
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U (2 * p) Z.regularThomClass)) := by
  have hc := SupportSheafCupCohomology.Constructions.Even.closedSupportGoodShiftSheafCup_cohomology (X := TopCat.of Z.regularAmbientSpace)
    Z.regularThomComplementOpen O U a (fun n hn => SheafPurity.Constructions.Construction.regularThomSheaf_exactAt_except Z n (by omega)) q
  rw [EvenCupShiftSections.Constructions.relativeEvenCocycleOpenRestriction_class, ha] at hc
  exact sourceTargetIso_cup
    (HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections (X := TopCat.of Z.regularAmbientSpace) O U) q)
    (HomologicalComplex.homologyMap
      (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z))) q)
    (HomologicalComplex.homologyMap
      (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
          Z.regularThomComplementOpen a)) q)
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) O U q)
    (ClosedSupportResolution.Constructions.Construction.regularSourceThomClosedSupportIso Z a ha O U q)
    (SupportedRelative.Constructions.Construction.regularThomClosedSupportRelativeIso Z O U q) _ _
    (HodgeConjecture.DegreeTwo.SupportedSourcePullback.Constructions.relativeSourcePullbackMap_cohomology (X := TopCat.of Z.regularAmbientSpace)
      (Y := TopCat.of Z.regularAnalyticSpace) O U (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) q)
    (ClosedSupportResolution.Constructions.Construction.regularSourceThomClosedSupportIso_cup Z a ha O U q) hc

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedSourceCup.Constructions.Construction
