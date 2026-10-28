import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourcePullback
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportSheafCupCohomology
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceIso

/-! # Source Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceCup.Constructions.HigherThom

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

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_cup (O U : Opens Z.regularAmbientSpace) (q : ℕ) :
    HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.SupportedSourcePullback.Constructions.relativeSourcePullbackMap
      (X := TopCat.of Z.regularAmbientSpace) (Y := TopCat.of Z.regularAnalyticSpace)
      O U (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)) q ≫
        (SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha O U q).hom =
      ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace) (O : Set Z.regularAmbientSpace) U)
        (Z.regularThomComplementOpen.isOpen.preimage continuous_subtype_val)
        (O.isOpen.preimage continuous_subtype_val) (2 * p) q
        (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U (2 * p) Z.regularThomClass)) := by
  have hc := SupportSheafCupCohomology.Constructions.Even.closedSupportGoodShiftSheafCup_cohomology (X := TopCat.of Z.regularAmbientSpace)
    Z.regularThomComplementOpen O U a (fun n hn => HodgeConjecture.DegreeTwo.RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z n (by omega)) q
  rw [EvenCupShiftSections.Constructions.relativeEvenCocycleOpenRestriction_class, ha] at hc
  exact sourceTargetIso_cup
    (HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections (X := TopCat.of Z.regularAmbientSpace) O U) q)
    (HomologicalComplex.homologyMap
      (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z))) q)
    (HomologicalComplex.homologyMap
      (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
          Z.regularThomComplementOpen a)) q)
    (HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) O U q)
    (Closed.SupportResolution.Constructions.HigherThom.regularSourceThomClosedSupportIso Z a ha O U q)
    (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O U q) _ _
    (HodgeConjecture.DegreeTwo.SupportedSourcePullback.Constructions.relativeSourcePullbackMap_cohomology (X := TopCat.of Z.regularAmbientSpace)
      (Y := TopCat.of Z.regularAnalyticSpace) O U (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) q)
    (Closed.SupportResolution.Constructions.HigherThom.regularSourceThomClosedSupportIso_cup Z a ha O U q) hc

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceCup.Constructions.HigherThom
