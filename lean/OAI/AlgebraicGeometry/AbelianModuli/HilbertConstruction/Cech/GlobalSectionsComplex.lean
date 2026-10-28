/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationNaturality

/-! # Global Sections Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalSectionsComplex.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)
local instance : (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

/-- Applying global sections degreewise to the sheaf-level Cech complex gives the
native Cech complex of the underlying presheaf. -/
noncomputable def cechGlobalSectionsComplexIso :
    ((HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj (IntrinsicCech.SheafComplex.cechComplex F U) ≅
      (cechComplexFunctor U).obj F.obj :=
  HomologicalComplex.Hom.isoOfComponents (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U) (by
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst j
    change (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U i).hom ≫
        ((cechComplexFunctor U).obj F.obj).d i (i + 1) =
      (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map ((IntrinsicCech.SheafComplex.cechComplex F U).d i (i + 1)) ≫
        (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U (i + 1)).hom
    rw [IntrinsicCech.SheafComplex.cechComplex_d F U i]
    change
      ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).hom.app
            (IntrinsicCech.SheafTerms.cechTerm F U i) ≫
          (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom) ≫
          ((cechComplexFunctor U).obj F.obj).d i (i + 1) =
        (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafDifferential.IntrinsicCech.cechDifferential F U i) ≫
          ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
              (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).hom.app
                (IntrinsicCech.SheafTerms.cechTerm F U (i + 1)) ≫
            (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom)
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
    calc
      ((eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U i) ≫
          (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom) ≫
          ((cechComplexFunctor U).obj F.obj).d i (i + 1)) =
        eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U i) ≫
          ((TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom ≫
            ((cechComplexFunctor U).obj F.obj).d i (i + 1)) :=
        Category.assoc _ _ _
      _ = eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U i) ≫
          ((SheafDifferential.IntrinsicCech.cechDifferential F U i).hom.app (op ⊤) ≫
            (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom) :=
        congrArg (fun f => eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U i) ≫ f)
          (TopSectionDifferential.IntrinsicCech.cechTopSectionsAddEquiv_d (F := F) (U := U) i)
      _ = (eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U i) ≫
            (SheafDifferential.IntrinsicCech.cechDifferential F U i).hom.app (op ⊤)) ≫
          (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom :=
        (Category.assoc _ _ _).symm
      _ = ((HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafDifferential.IntrinsicCech.cechDifferential F U i) ≫
            eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U (i + 1))) ≫
          (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom :=
        congrArg (fun f => f ≫
          (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom)
            (eΓ.hom.naturality (SheafDifferential.IntrinsicCech.cechDifferential F U i)).symm
      _ = (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).map (SheafDifferential.IntrinsicCech.cechDifferential F U i) ≫
          (eΓ.hom.app (IntrinsicCech.SheafTerms.cechTerm F U (i + 1)) ≫
            (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom) :=
        Category.assoc _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalSectionsComplex.IntrinsicCech
