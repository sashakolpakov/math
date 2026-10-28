/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitScalar
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackUnitMonoidal
import Mathlib.CategoryTheory.Monoidal.Mon

/-! # Tensor Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections

open _root_.AlgebraicGeometry _root_.CategoryTheory Limits MonoidalCategory _root_.SheafOfModules _root_.TopologicalSpace
universe v u

set_option backward.isDefEq.respectTransparency false in
local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) := by
  change (PresheafOfModules.sheafification
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsLocalization
    (OfModulesMonoidal.PresheafOfModules.sheafificationW
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj))
  infer_instance

local instance (X : Scheme.{u}) :
    (OfModulesMonoidal.PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal := by
  change (OfModulesMonoidal.PresheafOfModules.sheafificationW
    (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsMonoidal
  infer_instance

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Projective.Monoidal.Scheme.Modules.monoidalCategory X

noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules X.ringCatSheaf) := by
  change MonoidalCategory X.Modules
  exact Projective.Monoidal.Scheme.Modules.monoidalCategory X

noncomputable local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (W := OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
    (Iso.refl _)).Monoidal)

/-- The localized monoidal unit is the structure sheaf. -/
noncomputable def monoidalUnitObjIso (X : Scheme.{u}) :
    𝟙_ X.Modules ≅ Invertible.Scheme.Modules.unitObj X :=
  Invertible.Scheme.Modules.sheafifyValIso (Invertible.Scheme.Modules.unitObj X)

/-- The section `1` of the structure module, transported to the localized
monoidal unit. -/
noncomputable def monoidalUnitSection (X : Scheme.{u}) :
    Γ(𝟙_ X.Modules, (⊤ : X.Opens)) :=
  (monoidalUnitObjIso X).inv.val.app (.op ⊤)
    (show X.presheaf.obj (.op ⊤) from 1)

/-- The explicit structure module is the monoidal unit, so its tensor square is
canonically the structure module again. -/
noncomputable def unitObjTensorIso (X : Scheme.{u}) :
    Invertible.Scheme.Modules.unitObj X ⊗ Invertible.Scheme.Modules.unitObj X ≅
      Invertible.Scheme.Modules.unitObj X :=
  ((monoidalUnitObjIso X).symm ⊗ᵢ (monoidalUnitObjIso X).symm) ≪≫
    λ_ (𝟙_ X.Modules) ≪≫ monoidalUnitObjIso X

/-- The canonical multiplication on the explicit structure module is associative. -/
theorem unitObjTensorIso_hom_assoc (X : Scheme.{u}) :
    (α_ (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X)
          (Invertible.Scheme.Modules.unitObj X)).inv ≫
        ((unitObjTensorIso X).hom ⊗ₘ 𝟙 (Invertible.Scheme.Modules.unitObj X)) ≫
          (unitObjTensorIso X).hom =
      (𝟙 (Invertible.Scheme.Modules.unitObj X) ⊗ₘ (unitObjTensorIso X).hom) ≫
        (unitObjTensorIso X).hom := by
  let : MonObj (Invertible.Scheme.Modules.unitObj X) :=
    MonObj.ofIso (monoidalUnitObjIso X)
  change (α_ (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X)
        (Invertible.Scheme.Modules.unitObj X)).inv ≫
      (MonObj.mul ⊗ₘ 𝟙 (Invertible.Scheme.Modules.unitObj X)) ≫ MonObj.mul =
    (𝟙 (Invertible.Scheme.Modules.unitObj X) ⊗ₘ MonObj.mul) ≫ MonObj.mul
  simpa only [tensorHom_id, id_tensorHom] using
    (MonObj.mul_assoc_flip (Invertible.Scheme.Modules.unitObj X)).symm

/-- Associativity of a multiplication propagates through three morphisms into
its underlying object. -/
theorem tensorMulHom_assoc
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A B C X : D} (a : A ⟶ X) (b : B ⟶ X) (c : C ⟶ X)
    (mul : X ⊗ X ⟶ X)
    (hassoc :
      (α_ X X X).inv ≫ (mul ⊗ₘ 𝟙 X) ≫ mul =
        (𝟙 X ⊗ₘ mul) ≫ mul) :
    (α_ A B C).inv ≫ (((a ⊗ₘ b) ≫ mul) ⊗ₘ c) ≫ mul =
      (a ⊗ₘ ((b ⊗ₘ c) ≫ mul)) ≫ mul := by
  calc
    _ = (α_ A B C).inv ≫
        (((a ⊗ₘ b) ⊗ₘ c) ≫ (mul ⊗ₘ 𝟙 X)) ≫ mul := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id]
    _ = ((a ⊗ₘ (b ⊗ₘ c)) ≫ (α_ X X X).inv) ≫
        (mul ⊗ₘ 𝟙 X) ≫ mul := by
      rw [associator_inv_naturality]
      simp only [Category.assoc]
    _ = (a ⊗ₘ (b ⊗ₘ c)) ≫ (𝟙 X ⊗ₘ mul) ≫ mul := by
      simp only [Category.assoc, hassoc]
    _ = _ := by
      rw [← Category.assoc]
      rw [tensorHom_comp_tensorHom]
      rw [Category.comp_id]

/-- Conjugating the tensor of two endomorphisms through an identification with the
monoidal unit gives their composite. -/
theorem tensorUnitIso_hom_naturality
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X : D} (e : 𝟙_ D ≅ X) (f g : X ⟶ X) :
    (f ⊗ₘ g) ≫ (e.inv ⊗ₘ e.inv) ≫ (λ_ (𝟙_ D)).hom ≫ e.hom =
      (e.inv ⊗ₘ e.inv) ≫ (λ_ (𝟙_ D)).hom ≫ e.hom ≫ f ≫ g := by
  let a : 𝟙_ D ⟶ 𝟙_ D := e.hom ≫ f ≫ e.inv
  let b : 𝟙_ D ⟶ 𝟙_ D := e.hom ≫ g ≫ e.inv
  have hf : f ≫ e.inv = e.inv ≫ a := by
    simp [a]
  have hg : g ≫ e.inv = e.inv ≫ b := by
    simp [b]
  have hab : (a ⊗ₘ b) ≫ (λ_ (𝟙_ D)).hom =
      (λ_ (𝟙_ D)).hom ≫ a ≫ b := by
    rw [tensorHom_def, Category.assoc, leftUnitor_naturality]
    rw [unitors_equal, ← Category.assoc, rightUnitor_naturality]
    rw [Category.assoc]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  rw [hf, hg, ← tensorHom_comp_tensorHom]
  rw [Category.assoc]
  rw [← Category.assoc (a ⊗ₘ b) (λ_ (𝟙_ D)).hom e.hom, hab]
  simp [a, b, Category.assoc]

/-- The tensor-square identification induced by `e: 𝟙 ≅ X` is compatible
with a morphism into `X`. -/
theorem tensorUnitIso_hom_naturality_left
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X Y : D} (e : 𝟙_ D ≅ X) (f : Y ⟶ X) :
    (f ⊗ₘ e.hom) ≫ (e.inv ⊗ₘ e.inv) ≫
        (λ_ (𝟙_ D)).hom ≫ e.hom =
      (ρ_ Y).hom ≫ f := by
  rw [← Category.assoc (f ⊗ₘ e.hom) (e.inv ⊗ₘ e.inv)]
  rw [tensorHom_comp_tensorHom]
  rw [e.hom_inv_id]
  rw [unitors_equal]
  have h := rightUnitor_naturality (f ≫ e.inv)
  calc
    _ = ((f ≫ e.inv ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ (𝟙_ D)).hom) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = (((f ≫ e.inv) ▷ 𝟙_ D) ≫ (ρ_ (𝟙_ D)).hom) ≫ e.hom := by
      rw [tensorHom_id]
    _ = ((ρ_ Y).hom ≫ (f ≫ e.inv)) ≫ e.hom :=
      congrArg (fun k ↦ k ≫ e.hom) h
    _ = _ := by simp

/-- Under `𝒪_X ⊗ 𝒪_X ≅ 𝒪_X`, tensoring multiplication by `r` and by `s`
is multiplication by `r * s`. -/
theorem unitObjTensorIso_hom_comp_scalars (X : Scheme.{u})
    (r s : Γ(X, (⊤ : X.Opens))) :
    (UnitScalar.unitEndomorphismOfTopSection r ⊗ₘ
        UnitScalar.unitEndomorphismOfTopSection s) ≫ (unitObjTensorIso X).hom =
      (unitObjTensorIso X).hom ≫ UnitScalar.unitEndomorphismOfTopSection (r * s) := by
  change (UnitScalar.unitEndomorphismOfTopSection r ⊗ₘ
      UnitScalar.unitEndomorphismOfTopSection s) ≫
      ((monoidalUnitObjIso X).inv ⊗ₘ (monoidalUnitObjIso X).inv) ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ (monoidalUnitObjIso X).hom =
    ((monoidalUnitObjIso X).inv ⊗ₘ (monoidalUnitObjIso X).inv) ≫
      (λ_ (𝟙_ X.Modules)).hom ≫ (monoidalUnitObjIso X).hom ≫
        UnitScalar.unitEndomorphismOfTopSection (r * s)
  calc
    _ = ((monoidalUnitObjIso X).inv ⊗ₘ (monoidalUnitObjIso X).inv) ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ (monoidalUnitObjIso X).hom ≫
          UnitScalar.unitEndomorphismOfTopSection r ≫ UnitScalar.unitEndomorphismOfTopSection s :=
      tensorUnitIso_hom_naturality (monoidalUnitObjIso X) _ _
    _ = _ := by rw [UnitScalar.unitEndomorphismOfTopSection_comp]

/-- The localized coherent tensor agrees with the explicit sheafified tensor used by
the cover-local invertibility API. -/
noncomputable def monoidalTensorObjIso {X : Scheme.{u}} (M N : X.Modules) :
    M ⊗ N ≅ Invertible.Scheme.Modules.tensorObj M N :=
  ((Invertible.Scheme.Modules.sheafifyValIso M).symm ⊗ᵢ
      (Invertible.Scheme.Modules.sheafifyValIso N).symm) ≪≫
    Localization.Monoidal.μ
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) M.val N.val

/-- The pure tensor of two sections over the same open, regarded as a section of the
localized tensor product of sheaves of modules. -/
noncomputable def tensorSection {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) : Γ(M ⊗ N, U) :=
  (monoidalTensorObjIso M N).inv.val.app (.op U)
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val)).app
        (.op U) (x ⊗ₜ y))

/-- The cotensorator of module sheafification is obtained by mapping the tensor of the
two sheafification units and then applying the canonical inverse tensor comparison. -/
theorem sheafification_δ_eq_map_unit_tensor_comp_monoidalTensorObjIso_inv
    {X : Scheme.{u}} (A B : X.PresheafOfModules) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    Functor.OplaxMonoidal.δ L A B =
      L.map (adj.unit.app A ⊗ₘ adj.unit.app B) ≫
        (monoidalTensorObjIso (L.obj A) (L.obj B)).inv := by
  dsimp only
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let cA := Invertible.Scheme.Modules.sheafifyValIso (L.obj A)
  let cB := Invertible.Scheme.Modules.sheafifyValIso (L.obj B)
  have hδ := Functor.OplaxMonoidal.δ_natural L
    (adj.unit.app A) (adj.unit.app B)
  change
    Functor.OplaxMonoidal.δ L A B ≫
        (L.map (adj.unit.app A) ⊗ₘ L.map (adj.unit.app B)) =
      L.map (adj.unit.app A ⊗ₘ adj.unit.app B) ≫
        Functor.OplaxMonoidal.δ L (L.obj A).val (L.obj B).val at hδ
  have hA : L.map (adj.unit.app A) ≫ cA.hom = 𝟙 (L.obj A) := by
    change L.map (adj.unit.app A) ≫ adj.counit.app (L.obj A) = 𝟙 (L.obj A)
    exact adj.left_triangle_components A
  have hB : L.map (adj.unit.app B) ≫ cB.hom = 𝟙 (L.obj B) := by
    change L.map (adj.unit.app B) ≫ adj.counit.app (L.obj B) = 𝟙 (L.obj B)
    exact adj.left_triangle_components B
  have hmono :
      (monoidalTensorObjIso (L.obj A) (L.obj B)).inv =
        (Localization.Monoidal.μ L
          (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
          (Iso.refl _) (L.obj A).val (L.obj B).val).inv ≫
            (cA.hom ⊗ₘ cB.hom) := rfl
  rw [hmono]
  change
    Functor.OplaxMonoidal.δ L A B =
      L.map (adj.unit.app A ⊗ₘ adj.unit.app B) ≫
        Functor.OplaxMonoidal.δ L (L.obj A).val (L.obj B).val ≫
          (cA.hom ⊗ₘ cB.hom)
  have hcancel :
      (L.map (adj.unit.app A) ⊗ₘ L.map (adj.unit.app B)) ≫
          (cA.hom ⊗ₘ cB.hom) = 𝟙 (L.obj A ⊗ L.obj B) := by
    calc
      _ = (L.map (adj.unit.app A) ≫ cA.hom) ⊗ₘ
          (L.map (adj.unit.app B) ≫ cB.hom) :=
        tensorHom_comp_tensorHom _ _ _ _
      _ = (𝟙 _) ⊗ₘ (𝟙 _) := congrArg₂ (· ⊗ₘ ·) hA hB
      _ = 𝟙 _ := by
        simpa only [Functor.id_obj] using id_tensorHom_id (L.obj A) (L.obj B)
  calc
    _ = Functor.OplaxMonoidal.δ L A B ≫ 𝟙 _ :=
      (Category.comp_id _).symm
    _ = Functor.OplaxMonoidal.δ L A B ≫
        ((L.map (adj.unit.app A) ⊗ₘ L.map (adj.unit.app B)) ≫
          (cA.hom ⊗ₘ cB.hom)) :=
      congrArg (Functor.OplaxMonoidal.δ L A B ≫ ·) hcancel.symm
    _ = (Functor.OplaxMonoidal.δ L A B ≫
          (L.map (adj.unit.app A) ⊗ₘ L.map (adj.unit.app B))) ≫
            (cA.hom ⊗ₘ cB.hom) :=
      Category.assoc _ _ _
    _ = (L.map (adj.unit.app A ⊗ₘ adj.unit.app B) ≫
          Functor.OplaxMonoidal.δ L (L.obj A).val (L.obj B).val) ≫
            (cA.hom ⊗ₘ cB.hom) :=
      congrArg (· ≫ (cA.hom ⊗ₘ cB.hom)) hδ
    _ = _ := (Category.assoc _ _ _).symm

/-- Applying the sheafification cotensorator to the unit image of a pure tensor gives
the canonical pure tensor section of the two unit images. -/
theorem sheafification_δ_unit_tmul_eq_tensorSection
    {X : Scheme.{u}} (A B : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (.op U)) (y : B.obj (.op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (Functor.OplaxMonoidal.δ L A B).val.app (.op U)
        ((adj.unit.app (A ⊗ B)).app (.op U) (x ⊗ₜ y)) =
      tensorSection (L.obj A) (L.obj B) U
        ((adj.unit.app A).app (.op U) x)
        ((adj.unit.app B).app (.op U) y) := by
  dsimp only
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let f := adj.unit.app A ⊗ₘ adj.unit.app B
  have hδ :=
    sheafification_δ_eq_map_unit_tensor_comp_monoidalTensorObjIso_inv A B
  have hδapp := congrArg
    (fun q => q.val.app (.op U)
      ((adj.unit.app (A ⊗ B)).app (.op U) (x ⊗ₜ y))) hδ
  conv_rhs at hδapp =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  have hnat := adj.unit.naturality f
  have hnatapp := congrArg (fun q => q.app (.op U) (x ⊗ₜ y)) hnat
  conv_lhs at hnatapp =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hnatapp =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  let S := X.sheaf.obj.obj (.op U)
  let AA : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact A.obj (.op U)
  let BB : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact B.obj (.op U)
  let LA : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact (L.obj A).val.obj (.op U)
  let LB : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact (L.obj B).val.obj (.op U)
  let uA : AA ⟶ LA := by
    change A.obj (.op U) ⟶ (L.obj A).val.obj (.op U)
    exact (adj.unit.app A).app (.op U)
  let uB : BB ⟶ LB := by
    change B.obj (.op U) ⟶ (L.obj B).val.obj (.op U)
    exact (adj.unit.app B).app (.op U)
  let xx : AA := x
  let yy : BB := y
  let x' : LA := uA xx
  let y' : LB := uB yy
  let t' : TensorProduct S LA LB := x' ⊗ₜ[S] y'
  have htmul : f.app (.op U) (x ⊗ₜ y) =
      (show ((L.obj A).val ⊗ (L.obj B).val).obj (.op U) from t') :=
    ModuleCat.MonoidalCategory.tensorHom_tmul uA uB xx yy
  change
    (adj.unit.app ((L.obj A).val ⊗ (L.obj B).val)).app (.op U)
        (f.app (.op U) (x ⊗ₜ y)) =
      (L.map f).val.app (.op U)
        ((adj.unit.app (A ⊗ B)).app (.op U) (x ⊗ₜ y)) at hnatapp
  unfold tensorSection
  exact hδapp.trans (congrArg
    (fun z => (monoidalTensorObjIso (L.obj A) (L.obj B)).inv.val.app (.op U) z)
    (hnatapp.symm.trans (congrArg
      (fun z => (adj.unit.app ((L.obj A).val ⊗ (L.obj B).val)).app (.op U) z)
      htmul)))

/-- Scalar multiplication may be moved between the two factors of a canonical
pure tensor section. -/
theorem tensorSection_smul {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (x : Γ(M, U)) (y : Γ(N, U)) :
    tensorSection M N U (a • x) y = tensorSection M N U x (a • y) := by
  unfold tensorSection
  let S := X.sheaf.obj.obj (.op U)
  let MM : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact M.val.obj (.op U)
  let NN : ModuleCat S := by
    change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
    exact N.val.obj (.op U)
  let aa : S := a
  let xx : MM := x
  let yy : NN := y
  have h : (aa • xx) ⊗ₜ[S] yy = xx ⊗ₜ[S] (aa • yy) :=
    TensorProduct.smul_tmul aa xx yy
  exact congrArg
    (fun q => (monoidalTensorObjIso M N).inv.val.app (.op U)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val)).app (.op U) q)) h

/-- If a structure-sheaf section annihilates a module section, then their
canonical pure tensor section is zero. -/
theorem tensorSection_eq_zero_of_smul_eq_zero
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (a : Γ(X, U)) (h : a • x = 0) :
    tensorSection M (Invertible.Scheme.Modules.unitObj X) U x
        (show Γ(Invertible.Scheme.Modules.unitObj X, U) from a) = 0 := by
  unfold tensorSection
  have hq :
      (x ⊗ₜ
        (show Γ(Invertible.Scheme.Modules.unitObj X, U) from a) :
          (M.val ⊗ (Invertible.Scheme.Modules.unitObj X).val).obj (.op U)) = 0 := by
    let S := X.sheaf.obj.obj (.op U)
    let MM : ModuleCat S := by
      change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
      exact M.val.obj (.op U)
    let AA : ModuleCat S := by
      change ModuleCat ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U))
      exact (Invertible.Scheme.Modules.unitObj X).val.obj (.op U)
    let xx : MM := x
    let aa : S := a
    let av : AA := show Γ(Invertible.Scheme.Modules.unitObj X, U) from a
    let onev : AA := show Γ(Invertible.Scheme.Modules.unitObj X, U) from
      (show Γ(X, U) from 1)
    have hav : av = aa • onev := by
      change a = a * 1
      rw [mul_one]
    have hx : aa • xx = 0 := h
    change (xx ⊗ₜ[S] av : TensorProduct S MM AA) = 0
    rw [hav]
    calc
      _ = (aa • xx) ⊗ₜ[S] onev :=
        (TensorProduct.smul_tmul aa xx onev).symm
      _ = 0 := by rw [hx, TensorProduct.zero_tmul]
  let η := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app
      (M.val ⊗ (Invertible.Scheme.Modules.unitObj X).val)).app (.op U)
  let e := (monoidalTensorObjIso M (Invertible.Scheme.Modules.unitObj X)).inv.val.app
    (.op U)
  change e.hom (η.hom
      (x ⊗ₜ (show Γ(Invertible.Scheme.Modules.unitObj X, U) from a))) = 0
  calc
    _ = e.hom (η.hom 0) := congrArg (fun q ↦ e.hom (η.hom q)) hq
    _ = e.hom 0 := congrArg e.hom (map_zero η.hom)
    _ = 0 := map_zero e.hom

/-- Forming a pure tensor section commutes with restriction to a smaller open. -/
theorem tensorSection_restrict {X : Scheme.{u}} (M N : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U) (x : Γ(M, U)) (y : Γ(N, U)) :
    (M ⊗ N).val.map (homOfLE hVU).op (tensorSection M N U x y) =
      tensorSection M N V
        (M.val.map (homOfLE hVU).op x)
        (N.val.map (homOfLE hVU).op y) := by
  let i := (homOfLE hVU).op
  let A := M.val ⊗ N.val
  let q := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app A
  let κ := (monoidalTensorObjIso M N).inv.val
  let t : A.obj (.op U) := x ⊗ₜ y
  have hq := q.naturality i
  have hqApply := ConcreteCategory.congr_hom hq t
  have hκ := κ.naturality i
  have hκApply := ConcreteCategory.congr_hom hκ (q.app (.op U) t)
  change (M ⊗ N).val.map i
      (κ.app (.op U) (q.app (.op U) t)) =
    κ.app (.op V)
      (q.app (.op V) (M.val.map i x ⊗ₜ N.val.map i y))
  conv_lhs at hκApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hκApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_lhs at hqApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hqApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have h₁ := hκApply.symm
  have h₂ := congrArg (κ.app (.op V)) hqApply.symm
  have hA : A.map i t =
      (M.val.map i x ⊗ₜ N.val.map i y : A.obj (.op V)) := by
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    rfl
  have h₃ := congrArg
    (fun a ↦ κ.app (.op V) (q.app (.op V) a)) hA
  exact h₁.trans (h₂.trans h₃)

/-- Restriction along an open immersion preserves the localized monoidal unit. -/
noncomputable def restrictMonoidalUnitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules := by
  letI : (Scheme.Modules.pullback f).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  exact (Scheme.Modules.restrictFunctorIsoPullback f).app (𝟙_ Y.Modules) ≪≫
    (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm

/-- Restriction along an open immersion preserves the localized tensor product. -/
noncomputable def restrictMonoidalTensorIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    (Scheme.Modules.restrictFunctor f).obj (M ⊗ N) ≅
      (Scheme.Modules.restrictFunctor f).obj M ⊗
        (Scheme.Modules.restrictFunctor f).obj N := by
  letI : (Scheme.Modules.pullback f).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  exact (Scheme.Modules.restrictFunctorIsoPullback f).app (M ⊗ N) ≪≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M ⊗ᵢ
      (Scheme.Modules.restrictFunctorIsoPullback f).symm.app N)

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
