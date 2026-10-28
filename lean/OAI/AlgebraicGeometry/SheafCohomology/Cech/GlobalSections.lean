/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.CategoryTheory.Adjunction.Additive
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Resolution
import OAI.AlgebraicGeometry.SheafCohomology.Cech.GlobalSectionsFunctor

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.GlobalSections.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Global sections of the sheaf-level Cech complex

This file identifies the complex obtained by applying global sections degreewise to the
sheaf-level Cech resolution with mathlib's native Cech complex of the underlying
presheaf. The comparison is compatible with the Cech differentials.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

noncomputable local instance : (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

private noncomputable def cechTopSectionsAddEquiv (n : ℕ) :
    (Terms.TopCat.Sheaf.cechTerm F U n).obj.obj (op ⊤) ≃+
      ((cechComplexFunctor U).obj F.obj).X n := by
  exact (Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n (⊤ : Opens X)).trans <|
    (AddEquiv.piCongrRight fun i =>
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).addCommGroupIsoToAddEquiv).trans <|
      (Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n).symm

private theorem cechTopSectionsAddEquiv_apply (n : ℕ)
    (x : (Terms.TopCat.Sheaf.cechTerm F U n).obj.obj (op ⊤))
    (i : Fin (n + 1) → ι) :
    Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n (cechTopSectionsAddEquiv F U n x) i =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).hom
          (Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x i) := by
  let y := (AddEquiv.piCongrRight fun i =>
    (F.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).addCommGroupIsoToAddEquiv)
        (Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x)
  exact congrFun ((Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n).apply_symm_apply y) i

private theorem addCommGrp_hom_map_sum {A B : AddCommGrpCat.{u}} {κ : Type*}
    [Fintype κ] (f : A ⟶ B) (x : κ → A) :
    ConcreteCategory.hom f (∑ k, x k) =
      ∑ k, ConcreteCategory.hom f (x k) :=
  by simp

private theorem cechTopRestriction_apply (n : ℕ) (k : Fin (n + 2))
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

private theorem cechTopCofaceSummand_apply (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) (x : (Terms.TopCat.Sheaf.cechTerm F U n).obj.obj (op ⊤)) :
    (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n (cechTopSectionsAddEquiv F U n x)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
        ((-1 : ℤ) ^ (k : ℕ) •
          F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
            (Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) := by
  have hSections := cechTopSectionsAddEquiv_apply (F := F) (U := U) n x
    (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  have hIdentify := congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) •
    F.obj.map (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i).op y) hSections
  have hRestrict := congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
    (cechTopRestriction_apply (F := F) (U := U) n k i
      (Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)))
  let restricted := F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
    (leOfHom (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
    (Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
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

private theorem cechTopAlternatingSum_apply (n : ℕ) (i : Fin (n + 2) → ι)
    (x : (Terms.TopCat.Sheaf.cechTerm F U n).obj.obj (op ⊤)) :
    (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n (cechTopSectionsAddEquiv F U n x)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
        (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
            (Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) := by
  let f := (F.obj.mapIso (eqToIso (congrArg op
    (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
  let a := fun k : Fin (n + 2) => (-1 : ℤ) ^ (k : ℕ) •
    F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
      (Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
  calc
    _ = ∑ k, ConcreteCategory.hom f (a k) :=
      Finset.sum_congr rfl (fun k _ =>
        cechTopCofaceSummand_apply (F := F) (U := U) n k i x)
    _ = ConcreteCategory.hom f (∑ k, a k) :=
      (addCommGrp_hom_map_sum f a).symm

private theorem cechTopSectionsAddEquiv_d (n : ℕ) :
    (cechTopSectionsAddEquiv F U n).toAddCommGrpIso.hom ≫
        ((cechComplexFunctor U).obj F.obj).d n (n + 1) =
      (SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom.app (op ⊤) ≫
        (cechTopSectionsAddEquiv F U (n + 1)).toAddCommGrpIso.hom := by
  ext x
  apply (Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U (n + 1)).injective
  funext i
  change Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U (n + 1)
      (((cechComplexFunctor U).obj F.obj).d n (n + 1)
        (cechTopSectionsAddEquiv F U n x)) i =
    Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U (n + 1)
      (cechTopSectionsAddEquiv F U (n + 1)
        ((SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom.app (op ⊤) x)) i
  have hNative := Differential.TopologicalSpace.cechDifferential_apply F.obj U n
    (cechTopSectionsAddEquiv F U n x) i
  have hSum := cechTopAlternatingSum_apply (F := F) (U := U) n i x
  have hDifferential := congrArg
    (F.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
    (SheafDifferential.TopCat.Sheaf.cechDifferential_apply F U n (⊤ : Opens X) x i).symm
  have hTarget := (cechTopSectionsAddEquiv_apply (F := F) (U := U) (n + 1)
    ((SheafDifferential.TopCat.Sheaf.cechDifferential F U n).hom.app (op ⊤) x) i).symm
  exact hNative.trans (hSum.trans (hDifferential.trans hTarget))

/-- Global sections of a sheaf-level Cech term agree with the corresponding term of
the native Cech complex of the underlying presheaf. -/
noncomputable def cechGlobalSectionsXIso (n : ℕ) :
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).obj (Terms.TopCat.Sheaf.cechTerm F U n) ≅
      ((cechComplexFunctor U).obj F.obj).X n :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app
        (Terms.TopCat.Sheaf.cechTerm F U n) ≪≫
    (cechTopSectionsAddEquiv F U n).toAddCommGrpIso

/-- Global sections followed by the sheaf-level Cech augmentation, identified
with degree zero of the native Cech complex. -/
noncomputable def cechGlobalSectionsAugmentation :
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).obj F ⟶ ((cechComplexFunctor U).obj F.obj).X 0 :=
  (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (Augmentation.TopCat.Sheaf.cechAugmentation F U) ≫
    (cechGlobalSectionsXIso F U 0).hom

/-- The global Cech augmentation restricts a global section to every
one-fold intersection in the cover. -/
private theorem cechGlobalSectionsAugmentation_apply
    (x : (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).obj F) (i : Fin 1 → ι) :
    Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0
        (cechGlobalSectionsAugmentation F U x) i =
      F.obj.map (homOfLE (show
        (∏ᶜ fun k : Fin 1 ↦ U (i k)) ≤ ⊤ from le_top)).op
        ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}
            isTerminalTop).hom.app F x) := by
  let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  let y := eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U 0)
    ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (Augmentation.TopCat.Sheaf.cechAugmentation F U) x)
  have hy : y = (Augmentation.TopCat.Sheaf.cechAugmentation F U).hom.app (op ⊤)
      (eΓ.hom.app F x) := by
    have h := ConcreteCategory.congr_hom
      (eΓ.hom.naturality (Augmentation.TopCat.Sheaf.cechAugmentation F U)) x
    simp only [ConcreteCategory.comp_apply] at h
    change eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U 0)
        ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (Augmentation.TopCat.Sheaf.cechAugmentation F U) x) =
      (Augmentation.TopCat.Sheaf.cechAugmentation F U).hom.app (op ⊤) (eΓ.hom.app F x) at h
    exact h
  change Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0
    ((cechTopSectionsAddEquiv F U 0).toAddCommGrpIso.hom y) i = _
  rw [hy]
  change Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0
    (cechTopSectionsAddEquiv F U 0
      ((Augmentation.TopCat.Sheaf.cechAugmentation F U).hom.app (op ⊤) (eΓ.hom.app F x))) i = _
  rw [cechTopSectionsAddEquiv_apply (F := F) (U := U) 0
    ((Augmentation.TopCat.Sheaf.cechAugmentation F U).hom.app (op ⊤) (eΓ.hom.app F x)) i]
  rw [Augmentation.TopCat.Sheaf.cechAugmentation_apply F U (⊤ : Opens X) (eΓ.hom.app F x) i]
  change (F.obj.map _ ≫ F.obj.map _) _ = F.obj.map _ _
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      (congrArg F.obj.map (Subsingleton.elim _ _))) _

/-- Public coordinate formula for the native degree-zero augmentation. -/
theorem cechGlobalSectionsAugmentation_coordinate
    (x : (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).obj F) (i : Fin 1 → ι) :
    Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0 (cechGlobalSectionsAugmentation F U x) i =
      F.obj.map (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op
        ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).hom.app F x) :=
  cechGlobalSectionsAugmentation_apply F U x i

/-- The global-sections Cech augmentation is natural in the sheaf. -/
theorem cechGlobalSectionsAugmentation_naturality
    {G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    cechGlobalSectionsAugmentation F U ≫
        ((cechComplexFunctor U).map f.hom).f 0 =
      (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map f ≫ cechGlobalSectionsAugmentation G U := by
  apply ConcreteCategory.hom_ext
  intro x
  apply (Cochains.TopologicalSpace.cechCochainAddEquiv G.obj U 0).injective
  funext i
  let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  have hnative :
      ((cechComplexFunctor U).map f.hom).f 0 ≫
          Limits.Pi.π (fun j : Fin 1 → ι ↦
            G.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i =
        Limits.Pi.π (fun j : Fin 1 → ι ↦
            F.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i ≫
          f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k))) := by
    change Limits.Pi.map (fun j : Fin 1 → ι ↦ f.hom.app
      (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) ≫ _ = _
    exact Limits.Pi.map_π _ i
  have hmap := ConcreteCategory.congr_hom hnative
    (cechGlobalSectionsAugmentation F U x)
  have hmap' :
      Cochains.TopologicalSpace.cechCochainAddEquiv G.obj U 0
          (((cechComplexFunctor U).map f.hom).f 0
            (cechGlobalSectionsAugmentation F U x)) i =
        f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k)))
          (Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0
            (cechGlobalSectionsAugmentation F U x) i) := by
    rw [Cochains.TopologicalSpace.cechCochainAddEquiv_apply, Cochains.TopologicalSpace.cechCochainAddEquiv_apply]
    change
      (Limits.Pi.π (fun j : Fin 1 → ι ↦
        G.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i)
          (((cechComplexFunctor U).map f.hom).f 0
            (cechGlobalSectionsAugmentation F U x)) =
        f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k)))
          ((Limits.Pi.π (fun j : Fin 1 → ι ↦
            F.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i)
              (cechGlobalSectionsAugmentation F U x))
    calc
      _ = (Limits.Pi.π (fun j : Fin 1 → ι ↦
            F.obj.obj (op (∏ᶜ fun k : Fin 1 ↦ U (j k)))) i ≫
          f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k))))
            (cechGlobalSectionsAugmentation F U x) := hmap
      _ = _ := rfl
  have hΓ := ConcreteCategory.congr_hom (eΓ.hom.naturality f) x
  simp only [ConcreteCategory.comp_apply] at hΓ
  have hΓ' :
      f.hom.app (op ⊤) (eΓ.hom.app F x) =
        eΓ.hom.app G ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map f x) := by
    exact hΓ.symm
  calc
    _ = f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k)))
        (Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0
          (cechGlobalSectionsAugmentation F U x) i) := hmap'
    _ = f.hom.app (op (∏ᶜ fun k : Fin 1 ↦ U (i k)))
        (F.obj.map (homOfLE le_top).op (eΓ.hom.app F x)) := by
      rw [cechGlobalSectionsAugmentation_apply]
    _ = G.obj.map (homOfLE le_top).op
        (f.hom.app (op ⊤) (eΓ.hom.app F x)) := by
      exact ConcreteCategory.congr_hom
        (f.hom.naturality (homOfLE le_top).op) _
    _ = G.obj.map (homOfLE le_top).op
        (eΓ.hom.app G ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map f x)) := by rw [hΓ']
    _ = Cochains.TopologicalSpace.cechCochainAddEquiv G.obj U 0
        (cechGlobalSectionsAugmentation G U ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map f x)) i := by
      rw [cechGlobalSectionsAugmentation_apply]
    _ = _ := rfl

/-- Applying global sections degreewise to the sheaf-level Cech complex gives the
native Cech complex of the underlying presheaf. -/
noncomputable def cechGlobalSectionsComplexIso :
    ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj (SheafComplex.TopCat.Sheaf.cechComplex F U) ≅
      (cechComplexFunctor U).obj F.obj :=
  HomologicalComplex.Hom.isoOfComponents (cechGlobalSectionsXIso F U) (by
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst j
    change (cechGlobalSectionsXIso F U i).hom ≫
        ((cechComplexFunctor U).obj F.obj).d i (i + 1) =
      (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map ((SheafComplex.TopCat.Sheaf.cechComplex F U).d i (i + 1)) ≫
        (cechGlobalSectionsXIso F U (i + 1)).hom
    rw [SheafComplex.TopCat.Sheaf.cechComplex_d F U i]
    change
      ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).hom.app
            (Terms.TopCat.Sheaf.cechTerm F U i) ≫
          (cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom) ≫
          ((cechComplexFunctor U).obj F.obj).d i (i + 1) =
        (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (SheafDifferential.TopCat.Sheaf.cechDifferential F U i) ≫
          ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
              (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).hom.app
                (Terms.TopCat.Sheaf.cechTerm F U (i + 1)) ≫
            (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom)
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
    calc
      ((eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U i) ≫
          (cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom) ≫
          ((cechComplexFunctor U).obj F.obj).d i (i + 1)) =
        eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U i) ≫
          ((cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom ≫
            ((cechComplexFunctor U).obj F.obj).d i (i + 1)) :=
        Category.assoc _ _ _
      _ = eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U i) ≫
          ((SheafDifferential.TopCat.Sheaf.cechDifferential F U i).hom.app (op ⊤) ≫
            (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom) :=
        congrArg (fun f => eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U i) ≫ f)
          (cechTopSectionsAddEquiv_d (F := F) (U := U) i)
      _ = (eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U i) ≫
            (SheafDifferential.TopCat.Sheaf.cechDifferential F U i).hom.app (op ⊤)) ≫
          (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom :=
        (Category.assoc _ _ _).symm
      _ = ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (SheafDifferential.TopCat.Sheaf.cechDifferential F U i) ≫
            eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U (i + 1))) ≫
          (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom :=
        congrArg (fun f => f ≫
          (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom)
            (eΓ.hom.naturality (SheafDifferential.TopCat.Sheaf.cechDifferential F U i)).symm
      _ = (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (SheafDifferential.TopCat.Sheaf.cechDifferential F U i) ≫
          (eΓ.hom.app (Terms.TopCat.Sheaf.cechTerm F U (i + 1)) ≫
            (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom) :=
        Category.assoc _ _ _)

/-- The global Cech augmentation followed by the first native Cech differential
is zero. -/
@[reassoc]
theorem cechGlobalSectionsAugmentation_comp_d :
    cechGlobalSectionsAugmentation F U ≫
      ((cechComplexFunctor U).obj F.obj).d 0 1 = 0 := by
  have hcomm := (cechGlobalSectionsComplexIso F U).hom.comm 0 1
  change (cechGlobalSectionsXIso F U 0).hom ≫
      ((cechComplexFunctor U).obj F.obj).d 0 1 =
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (SheafDifferential.TopCat.Sheaf.cechDifferential F U 0) ≫
      (cechGlobalSectionsXIso F U 1).hom at hcomm
  have hzero : Augmentation.TopCat.Sheaf.cechAugmentation F U ≫ SheafDifferential.TopCat.Sheaf.cechDifferential F U 0 = 0 :=
    Augmentation.TopCat.Sheaf.cechAugmentation_comp F U
  have hmapzero :
      (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (Augmentation.TopCat.Sheaf.cechAugmentation F U) ≫
        (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (SheafDifferential.TopCat.Sheaf.cechDifferential F U 0) = 0 := by
    calc
      _ = (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map
          (Augmentation.TopCat.Sheaf.cechAugmentation F U ≫ SheafDifferential.TopCat.Sheaf.cechDifferential F U 0) :=
        ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map_comp _ _).symm
      _ = (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map 0 := congrArg (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map hzero
      _ = 0 := (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map_zero _ _
  rw [cechGlobalSectionsAugmentation, Category.assoc, hcomm]
  rw [← Category.assoc, hmapzero, zero_comp]

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.GlobalSections.TopCat.Sheaf
