import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.CochainUnit
import OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedSupportIntersection
import OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingComponents

/-! # Nested Supported Cochain Unit -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.NestedSupportedCochainUnit

noncomputable section

section

/-! The actual relative comparison for intersected supports retains the native map that forgets one support. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingComponents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O C : Opens X)

theorem supportedIntersectionComplexIso_inv_inclusion
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    (ClosedSupportIntersection.supportedIntersectionComplexIso O C K).inv ≫
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C K) ≫
      CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C K = CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion (O ⊔ C) K := by
  apply (cancel_epi (ClosedSupportIntersection.supportedIntersectionComplexIso O C K).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (ClosedSupportIntersection.supportedIntersectionComplexIso_inclusion O C K).symm

def relativeToNestedSupportedFunctorGlobalSections :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X ((O ⊔ C) : Set X) ⟶
      HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (Supported.DerivedComparison.supportedSectionsFunctor O ⊤)
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) :=
  AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X (O ⊔ C) ≫
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (ClosedSupportIntersection.supportedIntersectionComplexIso O C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))).inv ≫
    (Supported.DerivedComparison.supportedSectionsFunctorIso O ⊤ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)).hom

theorem relativeToNestedSupportedFunctorGlobalSections_inclusion :
    relativeToNestedSupportedFunctorGlobalSections O C ≫
      Supported.CochainUnit.supportedSectionsCochainInclusion O ⊤ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X ((O ⊔ C) : Set X) ≫
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X := by
  unfold relativeToNestedSupportedFunctorGlobalSections
  simp only [Functor.mapIso_inv, Category.assoc]
  rw [← Category.assoc (Supported.DerivedComparison.supportedSectionsFunctorIso O ⊤
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)).hom,
    Supported.CochainUnit.supportedSectionsFunctorIso_inclusion]
  rw [← Functor.map_comp, ← Functor.map_comp]
  change AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X (O ⊔ C) ≫
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((ClosedSupportIntersection.supportedIntersectionComplexIso O C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).inv ≫
        CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion O (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)) ≫
        CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)) = _
  rw [supportedIntersectionComplexIso_inv_inclusion]
  exact AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections_inclusion (ModuleCat.of ℚ ℚ) X (O ⊔ C)

theorem relativeToNestedSupportedFunctorGlobalSections_forget :
    relativeToNestedSupportedFunctorGlobalSections O C ≫
      ((Supported.DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)) =
    AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap X (Set.subset_union_left : (O : Set X) ⊆ (O ⊔ C : Opens X)) ≫
      Supported.CochainUnit.relativeToSupportedFunctorGlobalSections O := by
  apply (cancel_mono (Supported.CochainUnit.supportedSectionsCochainInclusion O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))).mp
  rw [Category.assoc, Supported.CochainUnit.supportedSectionsCochainInclusion_naturality,
    relativeToNestedSupportedFunctorGlobalSections_inclusion,
    Category.assoc, Supported.CochainUnit.relativeToSupportedFunctorGlobalSections_inclusion,
    ← Category.assoc, AlgebraicTopology.Duality.Poincare.SupportConnectingComponents.relativeRationalSubsetCochainMap_inclusion]
  rfl

end

/-! The native relative cohomology isomorphisms preserve the original map that enlarges a support. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.SupportConnectingComponents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} [MetrizableSpace X] (O C : Opens X)

def relativeSupportedFunctorCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (O : Set X) n ≅
      (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (Supported.DerivedComparison.supportedSectionsFunctor O ⊤) (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).homology n := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable ℚ X O
  exact isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X O) n ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      (Supported.DerivedComparison.supportedSectionsFunctorIso O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))

theorem relativeSupportedFunctorCohomologyIso_hom (n : ℕ) :
    (relativeSupportedFunctorCohomologyIso O n).hom =
      HomologicalComplex.homologyMap (Supported.CochainUnit.relativeToSupportedFunctorGlobalSections O) n := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable ℚ X O
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap (_ ≫ _) n
  rw [HomologicalComplex.homologyMap_comp]

def relativeNestedSupportedCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X ((O ⊔ C) : Set X) n ≅
      (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (Supported.DerivedComparison.supportedSectionsFunctor O ⊤)
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)).homology n := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable ℚ X (O ⊔ C)
  exact isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) X (O ⊔ C)) n ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := X) ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
        (ClosedSupportIntersection.supportedIntersectionComplexIso O C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
      (Supported.DerivedComparison.supportedSectionsFunctorIso O ⊤ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C))

theorem relativeNestedSupportedCohomologyIso_hom (n : ℕ) :
    (relativeNestedSupportedCohomologyIso O C n).hom =
      HomologicalComplex.homologyMap (relativeToNestedSupportedFunctorGlobalSections O C) n := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable ℚ X (O ⊔ C)
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n ≫
    HomologicalComplex.homologyMap _ n = HomologicalComplex.homologyMap (_ ≫ _ ≫ _) n
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

theorem relativeNestedSupportedCohomologyIso_forget (n : ℕ) :
    (relativeNestedSupportedCohomologyIso O C n).hom ≫
      HomologicalComplex.homologyMap
        (((Supported.DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))) n =
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.subset_union_left : (O : Set X) ⊆ (O ⊔ C : Opens X)) n ≫
      (relativeSupportedFunctorCohomologyIso O n).hom := by
  rw [relativeNestedSupportedCohomologyIso_hom, relativeSupportedFunctorCohomologyIso_hom,
    ← HomologicalComplex.homologyMap_comp]
  rw [relativeToNestedSupportedFunctorGlobalSections_forget, HomologicalComplex.homologyMap_comp]

theorem relativeNestedSupportedCohomologyIso_inv_forget (n : ℕ) :
    (relativeNestedSupportedCohomologyIso O C n).inv ≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X (Set.subset_union_left : (O : Set X) ⊆ (O ⊔ C : Opens X)) n =
    HomologicalComplex.homologyMap
      (((Supported.DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))) n ≫
      (relativeSupportedFunctorCohomologyIso O n).inv := by
  apply (cancel_epi (relativeNestedSupportedCohomologyIso O C n).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, relativeNestedSupportedCohomologyIso_forget,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.NestedSupportedCochainUnit
