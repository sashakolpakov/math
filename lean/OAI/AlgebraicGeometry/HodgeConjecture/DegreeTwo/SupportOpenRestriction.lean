import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntersectSupportInclusion

/-! # Support Open Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportOpenRestriction.Constructions

noncomputable section

/-! Open restrictions of the supported comparison maps are the actual sheaf restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O : Opens X) {U W : Opens X} (i : U ⟶ W)

theorem closedSupportSectionRestriction_inclusion
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ) :
    (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionRestriction O i) (ComplexShape.up ℕ)).app K ≫
        ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O U K =
      ClosedSourceRelativeMap.Constructions.closedSupportSectionInclusion O W K ≫ CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsRestriction K i := by
  ext n : 1
  exact (CycleClass.Geometric.SheafClosedSupport.Cohomology.closedSupportSheafInclusion O (K.X n)).hom.naturality i.op

variable {Y : TopCat.{0}} (f : Y ⟶ X)

theorem closedSourceSupportedSectionsIso_open_naturality :
    (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionRestriction O i) (ComplexShape.up ℕ)).app
        (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) ≫ (ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O U).hom =
      (ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O W).hom ≫
        CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsRestriction (ModuleCat.of ℚ ℚ) Y ((Opens.map f).obj O)
          ((Opens.map f).map i) := by
  apply (cancel_mono (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafSectionsInclusion (ModuleCat.of ℚ ℚ) Y
    ((Opens.map f).obj O) ((Opens.map f).obj U))).mp
  rw [Category.assoc, ClosedSourceRelativeMap.Constructions.closedSourceSupportedSectionsIso_inclusion,
    closedSupportSectionRestriction_inclusion, Category.assoc,
    AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality.supportedSingularSheafSectionsInclusion_naturality, ← Category.assoc,
    ClosedSourceRelativeMap.Constructions.closedSourceSupportedSectionsIso_inclusion]
  rfl

theorem closedSourceRelativeToSupportedSections_open_naturality :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) Y (((Opens.map f).obj O : Opens Y) : Set Y)).map
        ((Opens.map f).map i).op ≫ ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections O U f =
      ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections O W f ≫
        (NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionRestriction O i) (ComplexShape.up ℕ)).app
          (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f) := by
  apply (cancel_mono (ClosedSupportIs.Constructions.closedSourceSupportedSectionsIso f O U).hom).mp
  unfold ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [closedSourceSupportedSectionsIso_open_naturality, Iso.inv_hom_id_assoc,
    AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality.relativeToSupportedSheafSections_naturality]

variable [MetrizableSpace Y]

theorem closedSourceSupportedRelativeCohomologyIso_open_naturality (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (SupportSectionChanges.Constructions.closedSupportSectionRestriction O i) (ComplexShape.up ℕ)).app
          (SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) f)) n ≫
        (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f O U n).hom =
      (ClosedSupportIs.Constructions.closedSourceSupportedRelativeCohomologyIso f O W n).hom ≫
        HomologicalComplex.homologyMap
          ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCochainPresheaf (ModuleCat.of ℚ ℚ) Y (((Opens.map f).obj O : Opens Y) : Set Y)).map
            ((Opens.map f).map i).op) n := by
  apply (cancel_epi (HomologicalComplex.homologyMap (ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections O W f) n)).mp
  erw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← closedSourceRelativeToSupportedSections_open_naturality,
    HomologicalComplex.homologyMap_comp, Category.assoc,
    ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections_homology, Category.comp_id,
    ← Category.assoc, ClosedSourceRelativeMap.Constructions.closedSourceRelativeToSupportedSections_homology, Category.id_comp]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportOpenRestriction.Constructions
