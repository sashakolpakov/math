/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TopSectionCoordinates

/-! # Top Section Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TopSectionDifferential.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)
local instance : (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

theorem cechTopCofaceSummand_apply (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) (x : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op ⊤)) :
    (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U n (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U n x)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
        ((-1 : ℤ) ^ (k : ℕ) •
          F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
            (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) := by
  have hSections := TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv_apply (F := F) (U := U) n x
    (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  have hIdentify := congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) •
    F.obj.map (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i).op y) hSections
  have hRestrict := congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
    (TopSectionCoordinates.IntrinsicCech.cechTopRestriction_apply (F := F) (U := U) n k i
      (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)))
  let restricted := F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
    (leOfHom (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
    (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
      (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
  have hScalar :
      (-1 : ℤ) ^ (k : ℕ) •
          (F.obj.mapIso (eqToIso (congrArg op
            (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom restricted =
        (F.obj.mapIso (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
          ((-1 : ℤ) ^ (k : ℕ) • restricted) :=
    (map_zsmul (F.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom.hom
      ((-1 : ℤ) ^ (k : ℕ)) restricted).symm
  exact hIdentify.trans (hRestrict.trans hScalar)

theorem cechTopAlternatingSum_apply (n : ℕ) (i : Fin (n + 2) → ι)
    (x : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op ⊤)) :
    (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U n (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U n x)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
        (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
            (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) := by
  let f := (F.obj.mapIso (eqToIso (congrArg op
    (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
  let a := fun k : Fin (n + 2) => (-1 : ℤ) ^ (k : ℕ) •
    F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
      (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
  calc
    _ = ∑ k, ConcreteCategory.hom f (a k) :=
      Finset.sum_congr rfl (fun k _ =>
        cechTopCofaceSummand_apply (F := F) (U := U) n k i x)
    _ = ConcreteCategory.hom f (∑ k, a k) :=
      (TopSectionCoordinates.IntrinsicCech.addCommGrp_hom_map_sum f a).symm

theorem cechTopSectionsAddEquiv_d (n : ℕ) :
    (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U n).toAddCommGrpIso.hom ≫
        ((cechComplexFunctor U).obj F.obj).d n (n + 1) =
      (SheafDifferential.IntrinsicCech.cechDifferential F U n).hom.app (op ⊤) ≫
        (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (n + 1)).toAddCommGrpIso.hom := by
  ext x
  apply (IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U (n + 1)).injective
  funext i
  change IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U (n + 1)
      (((cechComplexFunctor U).obj F.obj).d n (n + 1)
        (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U n x)) i =
    IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U (n + 1)
      (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U (n + 1)
        ((SheafDifferential.IntrinsicCech.cechDifferential F U n).hom.app (op ⊤) x)) i
  have hNative := IntrinsicCech.Differential.nativeCechDifferential_apply F.obj U n
    (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv F U n x) i
  have hSum := cechTopAlternatingSum_apply (F := F) (U := U) n i x
  have hDifferential := congrArg
    (F.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
    (SheafDifferential.IntrinsicCech.cechDifferential_apply F U n (⊤ : Opens X) x i).symm
  have hTarget := (TopSectionCoordinates.IntrinsicCech.cechTopSectionsAddEquiv_apply (F := F) (U := U) (n + 1)
    ((SheafDifferential.IntrinsicCech.cechDifferential F U n).hom.app (op ⊤) x) i).symm
  exact hNative.trans (hSum.trans (hDifferential.trans hTarget))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TopSectionDifferential.IntrinsicCech
