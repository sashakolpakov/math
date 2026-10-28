import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportShiftNaturality

/-! # Intersect Support Open Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportOpenNaturality.Constructions

noncomputable section

/-! The intersection-support and Thom comparisons commute with actual open restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (C O : Opens X) {U W : Opens X} (i : U ⟶ W)

theorem intersectSupportedSectionsIso_open_naturality
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionRestriction O i) (ComplexShape.up ℕ)).app
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≫ (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U K).hom =
      (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O W K).hom ≫
        CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex (C ⊔ O) K) i := by
  ext n : 1
  exact ((IntersectSupportComplex.Constructions.intersectSupportedComplexIso C O K).hom.f n).hom.naturality i.op

theorem relativeToIntersectSupportSections_open_naturality :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X ((C ⊔ O : Opens X) : Set X)).map i.op ≫
        IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections C O U =
      IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections C O W ≫
        (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionRestriction O i) (ComplexShape.up ℕ)).app
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) := by
  apply (cancel_mono (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).hom).mp
  have hi : (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionRestriction O i) (ComplexShape.up ℕ)).app
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) ≫
      (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).hom =
    (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O W (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).hom ≫
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsRestriction (ModuleCat.of ℚ ℚ) X (C ⊔ O) i :=
    intersectSupportedSectionsIso_open_naturality C O i (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)
  unfold IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hi, Iso.inv_hom_id_assoc, AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality.relativeToSupportedSheafSections_naturality]

variable [MetrizableSpace X]

theorem intersectSupportedRelativeCohomologyIso_open_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionRestriction O i) (ComplexShape.up ℕ)).app
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)) n ≫
        (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U n).hom =
      (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O W n).hom ≫
        HomologicalComplex.homologyMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) X ((C ⊔ O : Opens X) : Set X)).map i.op) n := by
  apply (cancel_epi (HomologicalComplex.homologyMap (IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections C O W) n)).mp
  erw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← relativeToIntersectSupportSections_open_naturality,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_homology, Category.comp_id,
    ← Category.assoc, IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_homology, Category.id_comp]

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem regularThomClosedSupportRelativeIso_open_naturality
    (O : Opens Z.regularAmbientSpace) {U W : Opens Z.regularAmbientSpace} (i : U ⟶ W) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          (SupportSectionChanges.Constructions.closedSupportSectionRestriction (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O i)
          (ComplexShape.up ℕ)).app (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)) n ≫
        (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O U n).hom =
      (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O W n).hom ≫
        HomologicalComplex.homologyMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
            ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace)).map i.op)
          (2*p+n) := by
  simp only [SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso, Iso.trans_hom]
  rw [← Category.assoc, ClosedSupportShiftNaturality.Constructions.closedSupportGoodShiftCohomologyIso_naturality,
    Category.assoc, intersectSupportedRelativeCohomologyIso_open_naturality,
    ← Category.assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportOpenNaturality.Constructions
