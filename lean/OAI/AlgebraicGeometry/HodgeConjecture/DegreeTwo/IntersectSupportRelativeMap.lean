import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportInclusion
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedThomRelative

/-! # Intersect Support Relative Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap.Constructions

noncomputable section

/-! The relative comparison for intersected supports retains the actual ambient relative cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (C O U : Opens X)

def relativeToIntersectSupportSections :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) ((C ⊔ O : Opens X) : Set X) U) ⟶
    GoodShiftFunctor.Constructions.functorCochainComplex (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U)
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) :=
  AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X (C ⊔ O) U ≫
    (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).inv

theorem relativeToIntersectSupportSections_inclusion :
    relativeToIntersectSupportSections C O U ≫
      IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) ((C ⊔ O : Opens X) : Set X) U) ≫
      AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X U := by
  unfold relativeToIntersectSupportSections
  rw [Category.assoc, ← IntersectSupportInclusion.Constructions.intersectSupportedSectionsIso_inclusion, Iso.inv_hom_id_assoc]
  exact AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections_inclusion (ModuleCat.of ℚ ℚ) X (C ⊔ O) U

variable [MetrizableSpace X]

instance relativeToIntersectSupportSections_quasiIso : QuasiIso (relativeToIntersectSupportSections C O U) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ X (C ⊔ O) U
  unfold relativeToIntersectSupportSections
  infer_instance

theorem relativeToIntersectSupportSections_homology (n : ℕ) :
    HomologicalComplex.homologyMap (relativeToIntersectSupportSections C O U) n ≫
      (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O U n).hom = 𝟙 _ := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafSections_of_metrizable ℚ X (C ⊔ O) U
  change HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X
    (C ⊔ O) U ≫ (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).inv) n ≫
    (HomologicalComplex.homologyMap (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).hom n ≫
      (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X (C ⊔ O) U) n).inv) = 𝟙 _
  rw [HomologicalComplex.homologyMap_comp, Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O U (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).inv n),
    ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id, HomologicalComplex.homologyMap_id,
    Category.id_comp]
  exact (isoOfQuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X (C ⊔ O) U) n).hom_inv_id

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap.Constructions
