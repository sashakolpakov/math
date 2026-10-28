/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalSectionsComplex

/-! # Global Augmentation Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationComplex.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)
local instance : (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

/-- The global Cech augmentation followed by the first native Cech differential
is zero. -/
@[reassoc]
theorem cechGlobalSectionsAugmentation_comp_d :
    GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U ≫
      ((cechComplexFunctor U).obj F.obj).d 0 1 = 0 := by
  have hcomm := (GlobalSectionsComplex.IntrinsicCech.cechGlobalSectionsComplexIso F U).hom.comm 0 1
  change (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 0).hom ≫
      ((cechComplexFunctor U).obj F.obj).d 0 1 =
    (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafDifferential.IntrinsicCech.cechDifferential F U 0) ≫
      (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 1).hom at hcomm
  have hzero : SheafAugmentation.IntrinsicCech.cechAugmentation F U ≫ SheafDifferential.IntrinsicCech.cechDifferential F U 0 = 0 :=
    SheafAugmentation.IntrinsicCech.cechAugmentation_comp F U
  have hmapzero :
      (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafAugmentation.IntrinsicCech.cechAugmentation F U) ≫
        (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafDifferential.IntrinsicCech.cechDifferential F U 0) = 0 := by
    calc
      _ = (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map
          (SheafAugmentation.IntrinsicCech.cechAugmentation F U ≫ SheafDifferential.IntrinsicCech.cechDifferential F U 0) :=
        ((HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map_comp _ _).symm
      _ = (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map 0 := congrArg (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map hzero
      _ = 0 := (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map_zero _ _
  rw [GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation, Category.assoc, hcomm]
  rw [← Category.assoc, hmapzero, zero_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationComplex.IntrinsicCech
