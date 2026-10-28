/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TopSectionDifferential

/-! # Global Augmentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)
local instance : (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

/-- Global sections of a sheaf-level Cech term agree with the corresponding term of
the native Cech complex of the underlying presheaf. -/
noncomputable def cechGlobalSectionsXIso (n : ℕ) :
    (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).obj (IntrinsicCech.SheafTerms.cechTerm F U n) ≅
      ((cechComplexFunctor U).obj F.obj).X n :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app
        (IntrinsicCech.SheafTerms.cechTerm F U n) ≪≫
    (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U n).toAddCommGrpIso

/-- Global sections followed by the sheaf-level Cech augmentation, identified
with degree zero of the native Cech complex. -/
noncomputable def cechGlobalSectionsAugmentation :
    (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).obj F ⟶ ((cechComplexFunctor U).obj F.obj).X 0 :=
  (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafAugmentation.IntrinsicCech.cechAugmentation F U) ≫
    (cechGlobalSectionsXIso F U 0).hom

/-- The global Cech augmentation restricts a global section to every
one-fold intersection in the cover. -/
theorem cechGlobalSectionsAugmentation_apply
    (x : (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).obj F) (i : Fin 1 → ι) :
    IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U 0
        (cechGlobalSectionsAugmentation F U x) i =
      F.obj.map (homOfLE (show
        (∏ᶜ fun k : Fin 1 ↦ U (i k)) ≤ ⊤ from le_top)).op
        ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}
            isTerminalTop).hom.app F x) := by
  let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  let y := eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U 0)
    ((HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafAugmentation.IntrinsicCech.cechAugmentation F U) x)
  have hy : y = (SheafAugmentation.IntrinsicCech.cechAugmentation F U).hom.app (op ⊤)
      (eΓ.hom.app F x) := by
    have h := ConcreteCategory.congr_hom
      (eΓ.hom.naturality (SheafAugmentation.IntrinsicCech.cechAugmentation F U)) x
    simp only [ConcreteCategory.comp_apply] at h
    change eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U 0)
        ((HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafAugmentation.IntrinsicCech.cechAugmentation F U) x) =
      (SheafAugmentation.IntrinsicCech.cechAugmentation F U).hom.app (op ⊤) (eΓ.hom.app F x) at h
    exact h
  change IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U 0
    ((TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U 0).toAddCommGrpIso.hom y) i = _
  rw [hy]
  change IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U 0
    (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U 0
      ((SheafAugmentation.IntrinsicCech.cechAugmentation F U).hom.app (op ⊤) (eΓ.hom.app F x))) i = _
  rw [TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv_apply (F := F) (U := U) 0
    ((SheafAugmentation.IntrinsicCech.cechAugmentation F U).hom.app (op ⊤) (eΓ.hom.app F x)) i]
  rw [SheafAugmentation.IntrinsicCech.cechAugmentation_apply F U (⊤ : Opens X) (eΓ.hom.app F x) i]
  change (F.obj.map _ ≫ F.obj.map _) _ = F.obj.map _ _
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      (congrArg F.obj.map (Subsingleton.elim _ _))) _

/-- Public coordinate formula for the native degree-zero augmentation. -/
theorem cechGlobalSectionsAugmentation_coordinate
    (x : (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).obj F) (i : Fin 1 → ι) :
    IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U 0 (cechGlobalSectionsAugmentation F U x) i =
      F.obj.map (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op
        ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).hom.app F x) :=
  cechGlobalSectionsAugmentation_apply F U x i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentation.IntrinsicCech
