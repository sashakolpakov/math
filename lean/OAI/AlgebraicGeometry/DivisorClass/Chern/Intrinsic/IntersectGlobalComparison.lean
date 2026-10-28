import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SourceGlobalComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.NestedSupportedCochainUnit
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap

/-! # Intersect Global Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.IntersectGlobalComparison

noncomputable section

/-! The native global Thom target uses the same original relative comparison for the intersected support. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def relativeRationalCochainCongr (X : TopCat.{0}) {A B : Set X} (h : A = B) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A ≅ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B :=
  eqToIso (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X) h)

theorem relativeRationalCochainCongr_inclusion (X : TopCat.{0}) {A B : Set X} (h : A = B) :
    (relativeRationalCochainCongr X h).hom ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A := by
  subst B
  exact Category.id_comp _

theorem relativeRationalCochainCongr_homology (X : TopCat.{0}) {A B : Set X} (h : A = B) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeRationalCochainCongr X h).hom n =
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X h n).hom := by
  subst B
  exact HomologicalComplex.homologyMap_id _ _

variable {X : TopCat.{0}} (O C : Opens X)

theorem supportUnion_comm : ((O ⊔ C) : Set X) = ((C ⊔ O) : Set X) := by rw [sup_comm]

theorem intersectSupportedSectionsIso_inv_inclusion :
    (HodgeConjecture.DegreeTwo.IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).inv ≫
      HodgeConjecture.DegreeTwo.IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) ⊤ =
    CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) X (C ⊔ O) ⊤ := by
  rw [← HodgeConjecture.DegreeTwo.IntersectSupportInclusion.Constructions.intersectSupportedSectionsIso_inclusion C O (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) ⊤,
    Iso.inv_hom_id_assoc]
  rfl

theorem relativeToNestedSupportedFunctorGlobalSections_native :
    NestedSupportedCochainUnit.relativeToNestedSupportedFunctorGlobalSections O C =
      (relativeRationalCochainCongr X (supportUnion_comm O C)).hom ≫
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) X ((C ⊔ O) : Set X)).inv ≫
      HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections C O ⊤ := by
  apply (cancel_mono (HodgeConjecture.DegreeTwo.IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) ⊤)).mp
  have hleft : NestedSupportedCochainUnit.relativeToNestedSupportedFunctorGlobalSections O C ≫
      HodgeConjecture.DegreeTwo.IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) ⊤ =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X ((O ⊔ C) : Set X) ≫
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X := by
    change NestedSupportedCochainUnit.relativeToNestedSupportedFunctorGlobalSections O C ≫
      (HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O ⊤ (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)) ≫ _) = _
    rw [← SourceGlobalComparison.supportedSectionsCochainInclusion_eq_native]
    exact NestedSupportedCochainUnit.relativeToNestedSupportedFunctorGlobalSections_inclusion O C
  rw [hleft]
  have hright : ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) X ((C ⊔ O) : Set X)).inv ≫
      HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections C O ⊤) ≫
      HodgeConjecture.DegreeTwo.IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion C O (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) ⊤ =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X ((C ⊔ O) : Set X) ≫
      AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℚ ℚ) X := by
    change ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheafTopIso (ModuleCat.of ℚ ℚ) X ((C ⊔ O) : Set X)).inv ≫
      (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections (ModuleCat.of ℚ ℚ) X (C ⊔ O) ⊤ ≫
        (HodgeConjecture.DegreeTwo.IntersectSupportComplex.Constructions.intersectSupportedSectionsIso C O ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)).inv)) ≫ _ = _
    rw [Category.assoc, Category.assoc, intersectSupportedSectionsIso_inv_inclusion, ← Category.assoc]
    exact AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections_inclusion (ModuleCat.of ℚ ℚ) X (C ⊔ O)
  rw [Category.assoc, hright, ← Category.assoc, relativeRationalCochainCongr_inclusion]

variable [MetrizableSpace X]

theorem relativeNestedSupportedCohomologyIso_native (n : ℕ) :
    NestedSupportedCochainUnit.relativeNestedSupportedCohomologyIso O C n =
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X (supportUnion_comm O C) n ≪≫
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) X ((C ⊔ O) : Set X) n).symm ≪≫
      (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O ⊤ n).symm := by
  have hn : HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections C O ⊤) n =
      (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O ⊤ n).inv := by
    apply (cancel_mono (HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso C O ⊤ n).hom).mp
    rw [HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_homology, Iso.inv_hom_id]
  apply Iso.ext
  rw [NestedSupportedCochainUnit.relativeNestedSupportedCohomologyIso_hom, relativeToNestedSupportedFunctorGlobalSections_native,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    relativeRationalCochainCongr_homology, hn]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.IntersectGlobalComparison
