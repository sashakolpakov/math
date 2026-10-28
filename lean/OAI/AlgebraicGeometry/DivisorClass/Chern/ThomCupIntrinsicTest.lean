import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedThomFunctorModel
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.CupCocycles

/-! # Thom Cup Intrinsic Test -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ThomCupIntrinsicTest

noncomputable section

/-! The original supported Thom cup on every relative test is the native absolute-relative cup after forgetting the divisor support. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)

def regularSupportedThomRelativeCup (O : Opens D.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (O : Set D.regularAmbientSpace) n ⟶
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      ((O ⊔ D.regularThomComplementOpen) : Set D.regularAmbientSpace) (2+n) :=
    HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace) O) n ≫
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of D.regularAmbientSpace) ⊤).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
          (Supported.SectionQuasiIso.supportedSheafComplexMap (X := TopCat.of D.regularAmbientSpace) O
            (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of D.regularAmbientSpace)
              D.regularThomComplementOpen a))) n ≫
      (Supported.ThomCupStage.regularSupportedThomGlobalRelativeIso D O n).hom

theorem regularSupportedThomCup_native_test (O : Opens D.regularAmbientSpace) (n : ℕ) :
    regularSupportedThomRelativeCup D a O n ≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap (TopCat.of D.regularAmbientSpace)
        (Set.subset_union_left : (O : Set D.regularAmbientSpace) ⊆
          (O ⊔ D.regularThomComplementOpen : Opens D.regularAmbientSpace)) (2+n) =
    ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) (TopCat.of D.regularAmbientSpace)
      (O : Set D.regularAmbientSpace) 2 n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (D.regularThomComplementOpen : Set D.regularAmbientSpace) 2 (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a))) := by
  unfold regularSupportedThomRelativeCup
  let X := TopCat.of D.regularAmbientSpace
  let A := HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X
  let T := HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex D
  let g := HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X D.regularThomComplementOpen a
  let G := (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n
  have hnat : H.map (G.map (Supported.SectionQuasiIso.supportedSheafComplexMap (X := X) O g)) ≫
      H.map (Supported.DerivedComparison.supportedSectionsFunctorIso (X := X) O ⊤ T).hom =
    H.map (Supported.DerivedComparison.supportedSectionsFunctorIso (X := X) O ⊤ A).hom ≫
      H.map (((Supported.DerivedComparison.supportedSectionsFunctor (X := X) O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map g) := by
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (Supported.DerivedComparison.supportedSectionsFunctorIso_naturality (X := X) O ⊤ g)
  have hunit : H.map (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X O) ≫
      H.map (Supported.DerivedComparison.supportedSectionsFunctorIso (X := X) O ⊤ A).hom =
    H.map (Supported.CochainUnit.relativeToSupportedFunctorGlobalSections (X := X) O) := by
    rw [← H.map_comp]
    rfl
  apply (cancel_mono (NestedSupportedCochainUnit.relativeSupportedFunctorCohomologyIso
    (X := TopCat.of D.regularAmbientSpace) O (2+n)).hom).mp
  simp only [Category.assoc]
  rw [SupportedThomFunctorModel.regularSupportedThomGlobalRelativeIso_forget]
  change H.map (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X O) ≫
    H.map (G.map (Supported.SectionQuasiIso.supportedSheafComplexMap (X := X) O g)) ≫ H.map (Supported.DerivedComparison.supportedSectionsFunctorIso (X := X) O ⊤ T).hom ≫ _ = _
  rw [← Category.assoc (H.map (G.map (Supported.SectionQuasiIso.supportedSheafComplexMap (X := X) O g))), hnat]
  simp only [Category.assoc]
  rw [← Category.assoc (H.map (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X O)), hunit,
    NestedSupportedCochainUnit.relativeSupportedFunctorCohomologyIso_hom]
  exact Supported.CupCocycles.supportedRelativeTwoCup_cohomology X D.regularThomComplementOpen O a
    (SupportedThomFunctorModel.regularSupportedThomBoundaryPreservation D O) n

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ThomCupIntrinsicTest
