import OAI.AlgebraicGeometry.DivisorClass.Chern.NestedSupportedCochainUnit
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.ThomCupStage
import OAI.AlgebraicGeometry.DivisorClass.Chern.GoodShiftFunctorRepresentatives

/-! # Supported Thom Functor Model -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedThomFunctorModel

noncomputable section

section

/-! The actual regular Thom comparison uses the same supported-section functor and native relative comparison as the cup calculation. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularSupportedThomBoundaryPreservation (O : Opens D.regularAmbientSpace)
    (n : ℕ) (hn : (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2).BoundaryGE n) :
    (Supported.DerivedComparison.supportedSectionsFunctor (X := TopCat.of D.regularAmbientSpace) O ⊤).PreservesRightHomologyOf
      (D.regularThomSheafComplex.sc (2+n)) := by
  have hn0 := HodgeConjecture.DegreeTwo.ThomShiftSections.Constructions.cochainDegreeShift_boundary_eq_zero 2 n hn
  subst n
  exact Supported.FlasqueExactness.supportedSections_preservesRightHomologyOf (X := TopCat.of D.regularAmbientSpace) O ⊤
    D.regularThomSheafComplex
    (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
      (TopCat.of D.regularAmbientSpace) D.regularThomComplementOpen)
    2 (fun i hi => HodgeConjecture.DegreeTwo.RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except D i (by omega)) 2 le_rfl

def regularSupportedThomFunctorRelativeIso (O : Opens D.regularAmbientSpace) (n : ℕ) :
    (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (Supported.DerivedComparison.supportedSectionsFunctor (X := TopCat.of D.regularAmbientSpace) O ⊤)
      (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex D)).homology n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      ((O ⊔ D.regularThomComplementOpen) : Set D.regularAmbientSpace) (2+n) :=
  GoodShiftFunctorRepresentatives.goodShiftFunctorHomologyIso (Supported.DerivedComparison.supportedSectionsFunctor (X := TopCat.of D.regularAmbientSpace) O ⊤)
      D.regularThomSheafComplex 2 (regularSupportedThomBoundaryPreservation D O) n ≪≫
    (NestedSupportedCochainUnit.relativeNestedSupportedCohomologyIso (X := TopCat.of D.regularAmbientSpace)
      O D.regularThomComplementOpen (2+n)).symm

theorem regularSupportedThomGlobalRelativeIso_functor (O : Opens D.regularAmbientSpace) (n : ℕ) :
    Supported.ThomCupStage.regularSupportedThomGlobalRelativeIso D O n =
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
        (Supported.DerivedComparison.supportedSectionsFunctorIso (X := TopCat.of D.regularAmbientSpace) O ⊤
          (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex D)) ≪≫ regularSupportedThomFunctorRelativeIso D O n := by
  apply Iso.ext
  unfold Supported.ThomCupStage.regularSupportedThomGlobalRelativeIso Supported.FlasqueExactness.supportedGoodShiftCohomologyIso
    regularSupportedThomFunctorRelativeIso GoodShiftFunctorRepresentatives.goodShiftFunctorHomologyIso NestedSupportedCochainUnit.relativeNestedSupportedCohomologyIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc]
  rfl

end

/-! Forgetting the original Thom support through the relative comparison retains the test support exactly. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularSupportedThomGlobalRelativeIso_forget (O : Opens D.regularAmbientSpace) (n : ℕ) :
    (Supported.ThomCupStage.regularSupportedThomGlobalRelativeIso D O n).hom ≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap (TopCat.of D.regularAmbientSpace)
        (Set.subset_union_left : (O : Set D.regularAmbientSpace) ⊆
          (O ⊔ D.regularThomComplementOpen : Opens D.regularAmbientSpace)) (2+n) ≫
      (NestedSupportedCochainUnit.relativeSupportedFunctorCohomologyIso (X := TopCat.of D.regularAmbientSpace) O (2+n)).hom =
    HomologicalComplex.homologyMap
      (Supported.DerivedComparison.supportedSectionsFunctorIso (X := TopCat.of D.regularAmbientSpace) O ⊤
        (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex D)).hom n ≫
      (GoodShiftFunctorRepresentatives.goodShiftFunctorHomologyIso (Supported.DerivedComparison.supportedSectionsFunctor (X := TopCat.of D.regularAmbientSpace) O ⊤)
        D.regularThomSheafComplex 2 (regularSupportedThomBoundaryPreservation D O) n).hom ≫
      HomologicalComplex.homologyMap
        (((Supported.DerivedComparison.supportedSectionsFunctor (X := TopCat.of D.regularAmbientSpace) O ⊤).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion D.regularThomComplementOpen
            (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of D.regularAmbientSpace)))) (2+n) := by
  rw [regularSupportedThomGlobalRelativeIso_functor]
  simp only [Iso.trans_hom, Functor.mapIso_hom, regularSupportedThomFunctorRelativeIso,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc (NestedSupportedCochainUnit.relativeNestedSupportedCohomologyIso (X := TopCat.of D.regularAmbientSpace)
      O D.regularThomComplementOpen (2+n)).inv,
    NestedSupportedCochainUnit.relativeNestedSupportedCohomologyIso_inv_forget]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedThomFunctorModel
