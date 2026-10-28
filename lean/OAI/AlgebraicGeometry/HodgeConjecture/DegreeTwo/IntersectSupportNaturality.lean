import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportRelativeMap
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportShiftNaturality

/-! # Intersect Support Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportNaturality.Constructions

noncomputable section

/-! Intersected-support comparisons commute with the original relative support inclusions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} {C D : Opens X} (h : C ≤ D) (U : Opens X)

def relativeOpenComplementChange :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (D : Set X) U) ⟶
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (𝟙 _) (fun _ hx => h hx)

theorem relativeOpenComplementChange_inclusion :
    relativeOpenComplementChange h U ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (C : Set X) U) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (D : Set X) U) := by
  unfold relativeOpenComplementChange
  rw [AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality, AlgebraicTopology.Cohomology.Singular.Functor.singularPullback_id, Category.comp_id]

variable (B : Opens X)

theorem relativeToIntersectSupportSections_support_naturality :
    relativeOpenComplementChange (sup_le_sup_left h B) U ≫ IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections B C U =
      IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections B D U ≫
        (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionChange h U) (ComplexShape.up ℕ)).app
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X B) := by
  have hi : (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionChange h U) (ComplexShape.up ℕ)).app
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X B) ≫
      IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion B C (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U =
    IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion B D (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U :=
    IntersectSupportInclusion.Constructions.intersectSupportSectionChange_inclusion B C (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) h U
  apply (cancel_mono (IntersectSupportInclusion.Constructions.intersectSupportSectionInclusion B C (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) U)).mp
  rw [Category.assoc, IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_inclusion,
    ← Category.assoc, relativeOpenComplementChange_inclusion,
    Category.assoc, hi,
    IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_inclusion]

variable [MetrizableSpace X]

theorem intersectSupportedRelativeCohomologyIso_support_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionChange h U) (ComplexShape.up ℕ)).app
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X B)) n ≫
        (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso B C U n).hom =
      (SupportedThomRelative.Constructions.intersectSupportedRelativeCohomologyIso B D U n).hom ≫
        HomologicalComplex.homologyMap (relativeOpenComplementChange (sup_le_sup_left h B) U) n := by
  apply (cancel_epi (HomologicalComplex.homologyMap (IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections B D U) n)).mp
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← relativeToIntersectSupportSections_support_naturality,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_homology, Category.comp_id,
    ← Category.assoc, IntersectSupportRelativeMap.Constructions.relativeToIntersectSupportSections_homology, Category.id_comp]

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem regularThomClosedSupportRelativeIso_support_naturality
    {O P : Opens Z.regularAmbientSpace} (h : O ≤ P) (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          (SupportSectionChanges.Constructions.closedSupportSectionChange (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) h U)
          (ComplexShape.up ℕ)).app (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)) n ≫
        (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z O U n).hom =
      (SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso Z P U n).hom ≫
        HomologicalComplex.homologyMap
          (relativeOpenComplementChange (X := TopCat.of Z.regularAmbientSpace)
            (sup_le_sup_left h Z.regularThomComplementOpen) U) (2*p+n) := by
  simp only [SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso, Iso.trans_hom]
  rw [← Category.assoc, ClosedSupportShiftNaturality.Constructions.closedSupportGoodShiftCohomologyIso_naturality,
    Category.assoc, intersectSupportedRelativeCohomologyIso_support_naturality,
    ← Category.assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportNaturality.Constructions
