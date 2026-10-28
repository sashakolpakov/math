/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafResolution
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.DerivedGlobalSections

/-! # Top Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TopSectionCoordinates.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
variable {X : TopCat.{u}}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)
local instance : (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.additiveSheafGlobalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

noncomputable def cechTopSectionsAddEquiv (n : ℕ) :
    (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op ⊤) ≃+
      ((cechComplexFunctor U).obj F.obj).X n := by
  exact (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n (⊤ : Opens X)).trans <|
    (AddEquiv.piCongrRight fun i =>
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).addCommGroupIsoToAddEquiv).trans <|
      (IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U n).symm

theorem cechTopSectionsAddEquiv_apply (n : ℕ)
    (x : (IntrinsicCech.SheafTerms.cechTerm F U n).obj.obj (op ⊤))
    (i : Fin (n + 1) → ι) :
    IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U n (cechTopSectionsAddEquiv F U n x) i =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).hom
          (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x i) := by
  let y := (AddEquiv.piCongrRight fun i =>
    (F.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).addCommGroupIsoToAddEquiv)
        (IntrinsicCech.SheafSectionCoordinates.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x)
  exact congrFun ((IntrinsicCech.Cochains.cechCochainAddEquiv F.obj U n).apply_symm_apply y) i

theorem addCommGrp_hom_map_sum {A B : AddCommGrpCat.{u}} {κ : Type*}
    [Fintype κ] (f : A ⟶ B) (x : κ → A) :
    ConcreteCategory.hom f (∑ k, x k) =
      ∑ k, ConcreteCategory.hom f (x k) :=
  by simp

theorem cechTopRestriction_apply (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι)
    (x : F.obj.obj (op ((⊤ : Opens X) ⊓
      ∏ᶜ fun a : Fin (n + 1) =>
        U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a)))) :
    F.obj.map (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
        ((F.obj.mapIso (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun a : Fin (n + 1) =>
            U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a)))))).hom x) =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun a : Fin (n + 2) => U (i a)))))).hom
        (F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op x) := by
  have h :
      F.obj.map (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun a : Fin (n + 1) =>
            U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a))))).hom ≫
          F.obj.map (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op =
        F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op ≫
          F.obj.map (eqToIso (congrArg op
            (top_inf_eq (∏ᶜ fun a : Fin (n + 2) => U (i a))))).hom := by
    exact (F.obj.map_comp _ _).symm.trans
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        (F.obj.map_comp _ _))
  exact ConcreteCategory.congr_hom h x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TopSectionCoordinates.IntrinsicCech
