import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportRelativeUnit

/-! # Supported Source Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourcePullback.Constructions

noncomputable section

/-! The supported source pullback is the actual pullback of relative singular cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U : Opens X)

theorem closedSupportSectionInclusion_naturality
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (g : K ⟶ L) :
    ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map g ≫
      ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U L =
    ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U K ≫
      ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map g := by
  change ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (((ClosedSupportIs.Constructions.closedSupportSheafFunctor O).mapHomologicalComplex (ComplexShape.up ℕ)).map g) ≫
    ((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections U).mapHomologicalComplex (ComplexShape.up ℕ)).map (ClosedSupportIs.Constructions.closedSupportCochainInclusion O L) = _
  rw [← Functor.map_comp, ClosedSupportComparison.Constructions.closedSupportCochainInclusion_naturality, Functor.map_comp]
  rfl

variable {Y : TopCat.{0}} (f : Y ⟶ X)

def relativeSourcePullbackMap :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := X) (O : Set X) U) ⟶
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of ((Opens.map f).obj U))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Y) (((Opens.map f).obj O : Opens Y) : Set Y) ((Opens.map f).obj U)) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) (SingularSheafPullback.Constructions.openPreimageMap f U) (fun _ hx => hx)

theorem relativeSourcePullbackMap_sections :
    ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U ≫
      ((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) f) =
    relativeSourcePullbackMap O U f ≫ ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections O U f := by
  apply (cancel_mono (ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U
    (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f))).mp
  rw [Category.assoc, closedSupportSectionInclusion_naturality, ← Category.assoc,
    ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections_inclusion, Category.assoc, ClosedSourceResolution.Constructions.singularSheafPullback_sections_unit,
    ← Category.assoc, Category.assoc (relativeSourcePullbackMap O U f),
    ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections_inclusion, ← Category.assoc]
  exact congrArg (fun g => g ≫ AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) Y ((Opens.map f).obj U))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) (SingularSheafPullback.Constructions.openPreimageMap f U) (fun _ hx => hx)).symm

variable [MetrizableSpace Y]

theorem relativeSourcePullbackMap_cohomology (n : ℕ) :
    HomologicalComplex.homologyMap (ClosedSupportRelativeUnit.Constructions.relativeToClosedSupportSections O U) n ≫
      HomologicalComplex.homologyMap
        (((ClosedSupportIs.Constructions.closedSupportSectionFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) f)) n ≫
        (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f O U n).hom =
    HomologicalComplex.homologyMap (relativeSourcePullbackMap O U f) n := by
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, relativeSourcePullbackMap_sections,
    HomologicalComplex.homologyMap_comp, Category.assoc, ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections_homology,
    Category.comp_id]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedSourcePullback.Constructions
