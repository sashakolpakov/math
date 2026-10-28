/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Evaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionUnit
import OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionIdentities

/-! # Tensor Frame Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections

open _root_.AlgebraicGeometry _root_.CategoryTheory Limits MonoidalCategory OAI.AlgebraicGeometry.SheafCohomology.Projective.Evaluation.SheafOfModules _root_.TopologicalSpace
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

theorem poleTensor_five_comp_of_three_eq
    {D : Type u} [Category.{v} D]
    {A₀ A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ : D}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂}
    {c : A₀ ⟶ B₁} {d : B₁ ⟶ A₂}
    {e : A₂ ⟶ A₃} {f : A₃ ⟶ A₄}
    {g : B₁ ⟶ B₂} {h : B₂ ⟶ A₄}
    {i : A₄ ⟶ A₅} {j : B₂ ⟶ B₃}
    {k : B₃ ⟶ A₅}
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ e ≫ f = g ≫ h)
    (h₃ : h ≫ i = j ≫ k) :
    a ≫ b ≫ e ≫ f ≫ i = c ≫ g ≫ j ≫ k := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

theorem poleTensor_nested_four_comp_of_tail_head_last
    {D : Type u} [Category.{v} D]
    {A₀ A₁ A₂ A₃ A₄ B₁ C₁ : D}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂}
    {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    {e : A₂ ⟶ B₁} {f : B₁ ⟶ A₄}
    {g : A₀ ⟶ C₁} {h : C₁ ⟶ B₁}
    {i : C₁ ⟶ A₄}
    (htail : c ≫ d = e ≫ f)
    (hhead : a ≫ b ≫ e = g ≫ h) (hlast : h ≫ f = i) :
    (a ≫ (b ≫ c)) ≫ d = g ≫ i := by
  calc
    (a ≫ (b ≫ c)) ≫ d = a ≫ ((b ≫ c) ≫ d) :=
      Category.assoc _ _ _
    _ = a ≫ (b ≫ (c ≫ d)) := congrArg
      (fun q ↦ a ≫ q) (Category.assoc _ _ _)
    _ = a ≫ (b ≫ (e ≫ f)) := congrArg
      (fun q ↦ a ≫ (b ≫ q)) htail
    _ = a ≫ ((b ≫ e) ≫ f) := congrArg
      (fun q ↦ a ≫ q) (Category.assoc _ _ _).symm
    _ = (a ≫ (b ≫ e)) ≫ f := (Category.assoc _ _ _).symm
    _ = (g ≫ h) ≫ f := congrArg (fun q ↦ q ≫ f) hhead
    _ = g ≫ (h ≫ f) := Category.assoc _ _ _
    _ = g ≫ i := congrArg (fun q ↦ g ≫ q) hlast

noncomputable def poleTensorTopSection
    {X : Scheme.{u}} (M N : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    Γ(M ⊗ N, (⊤ : X.Opens)) :=
  TensorSections.tensorSection M N ⊤ x y

noncomputable def poleTopSectionHom
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) : Invertible.Scheme.Modules.unitObj X ⟶ M :=
  M.unitHomEquiv.symm (AffineRankOne.globalSectionFamily M x)

theorem poleTopSectionHom_app_top_apply_one
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) :
    (poleTopSectionHom M x).val.app (.op ⊤)
      (show X.presheaf.obj (.op ⊤) from 1) = x := by
  change (M.unitHomEquiv (poleTopSectionHom M x)).val (.op ⊤) = x
  let s := AffineRankOne.globalSectionFamily M x
  have he : M.unitHomEquiv (poleTopSectionHom M x) = s :=
    Equiv.apply_symm_apply M.unitHomEquiv s
  have hv := congrArg (fun t ↦ t.val (.op (⊤ : X.Opens))) he
  rw [hv]
  change M.val.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op x = x
  simp
  rfl

theorem poleTopSectionHom_app_apply
    {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (W : X.Opens) (a : Γ(X, W)) :
    (poleTopSectionHom M x).val.app (.op W) a =
      a • M.presheaf.map
        (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op x := by
  rfl

theorem poleUnitObj_hom_ext_top
    {X : Scheme.{u}} {M : X.Modules}
    {f g : Invertible.Scheme.Modules.unitObj X ⟶ M}
    (h : f.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1) =
      g.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) :
    f = g := by
  apply SheafOfModules.hom_ext
  ext V
  let i := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
  have hf := PresheafOfModules.naturality_apply f.val i
    (show X.presheaf.obj (.op ⊤) from 1)
  have hg := PresheafOfModules.naturality_apply g.val i
    (show X.presheaf.obj (.op ⊤) from 1)
  change f.val.app V
      (X.presheaf.map i (show X.presheaf.obj (.op ⊤) from 1)) =
      M.presheaf.map i
        (f.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) at hf
  change g.val.app V
      (X.presheaf.map i (show X.presheaf.obj (.op ⊤) from 1)) =
      M.presheaf.map i
        (g.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) at hg
  rw [map_one] at hf hg
  exact hf.trans ((congrArg (fun q ↦ M.presheaf.map i q) h).trans hg.symm)

theorem poleTopSectionHom_localTrivializationRestriction
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (x : Γ(M, (⊤ : X.Opens))) :
    poleTopSectionHom ((Scheme.Modules.restrictFunctor U.1.ι).obj M)
        (FrameSections.localTrivializationRestriction M U x) =
      (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.1.ι).map
          (poleTopSectionHom M x) := by
  apply poleUnitObj_hom_ext_top
  rw [poleTopSectionHom_app_top_apply_one]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [SectionIdentities.Scheme.Modules.restrictUnitIso_inv_app_applyP]
  rw [map_one]
  unfold FrameSections.localTrivializationRestriction
  let s : Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    M.presheaf.map (eqToHom U.1.ι_image_top).op
      (M.presheaf.map
        (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op x)
  have hrestrict :
      (M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).inv s = s :=
    rfl
  have hmapApply :
      ((Scheme.Modules.restrictFunctor U.1.ι).map
          (poleTopSectionHom M x)).val.app (.op ⊤)
            (show X.presheaf.obj
              (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) =
        (poleTopSectionHom M x).val.app
          (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
            (show X.presheaf.obj
              (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) :=
    rfl
  have hs : s =
      (poleTopSectionHom M x).val.app
        (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
          (show X.presheaf.obj
            (.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) from 1) := by
    dsimp only [s]
    rw [poleTopSectionHom_app_apply, one_smul]
    change M.presheaf.map (eqToHom U.1.ι_image_top).op
        (M.presheaf.map
          (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op x) =
      M.presheaf.map
        (homOfLE (le_top : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) ≤
          (⊤ : X.Opens))).op x
    rw [← M.presheaf.map_comp_apply]
    rw [Subsingleton.elim
      ((homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op ≫
        (eqToHom U.1.ι_image_top).op)
      (homOfLE (le_top : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) ≤
        (⊤ : X.Opens))).op]
  exact hrestrict.trans (hs.trans hmapApply.symm)

theorem monoidalTensorObjIso_inv_natural
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map (f.val ⊗ₘ g.val) ≫
        (TensorSections.monoidalTensorObjIso M' N').inv =
      (TensorSections.monoidalTensorObjIso M N).inv ≫ (f ⊗ₘ g) := by
  let : (OfModulesMonoidal.PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @OfModulesMonoidal.PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  let : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let sh (A : X.PresheafOfModules) : X.Modules := L.obj A
  let δ (A B : X.PresheafOfModules) : sh (A ⊗ B) ⟶ sh A ⊗ sh B :=
    Functor.OplaxMonoidal.δ F A B
  let ε (A : X.Modules) : sh A.val ⟶ A :=
    (Invertible.Scheme.Modules.sheafifyValIso A).hom
  have hIso (A B : X.Modules) :
      (TensorSections.monoidalTensorObjIso A B).inv =
        δ A.val B.val ≫ (ε A ⊗ₘ ε B) := by
    rfl
  have hδ :
      L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val =
        δ M.val N.val ≫ (L.map f.val ⊗ₘ L.map g.val) :=
    (Functor.OplaxMonoidal.δ_natural F f.val g.val).symm
  have hεf : L.map f.val ≫ ε M' = ε M ≫ f :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality f
  have hεg : L.map g.val ≫ ε N' = ε N ≫ g :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.naturality g
  let e' : (sh M'.val ⊗ sh N'.val) ⟶ (M' ⊗ N') :=
    ε M' ⊗ₘ ε N'
  let e₀ : (sh M.val ⊗ sh N.val) ⟶ (M ⊗ N) :=
    ε M ⊗ₘ ε N
  let lfg : (sh M.val ⊗ sh N.val) ⟶ (sh M'.val ⊗ sh N'.val) :=
    L.map f.val ⊗ₘ L.map g.val
  let fg : (M ⊗ N) ⟶ (M' ⊗ N') := f ⊗ₘ g
  change L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val =
    δ M.val N.val ≫ lfg at hδ
  have hTensorComp : lfg ≫ e' = e₀ ≫ fg := by
    let c₁ : (sh M.val ⊗ sh N.val) ⟶ (M' ⊗ N') :=
      (L.map f.val ≫ ε M') ⊗ₘ (L.map g.val ≫ ε N')
    let c₀ : (sh M.val ⊗ sh N.val) ⟶ (M' ⊗ N') :=
      (ε M ≫ f) ⊗ₘ (ε N ≫ g)
    have hleft : lfg ≫ e' = c₁ := by
      dsimp only [lfg, e', c₁]
      exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    have hmiddle : c₁ = c₀ := by
      dsimp only [c₁, c₀]
      exact congrArg₂
        (fun (a : sh M.val ⟶ M') (b : sh N.val ⟶ N') ↦ a ⊗ₘ b)
        hεf hεg
    have hright : e₀ ≫ fg = c₀ := by
      dsimp only [e₀, fg, c₀]
      exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
    exact hleft.trans (hmiddle.trans hright.symm)
  rw [hIso M' N', hIso M N]
  change L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val ≫ e' =
    δ M.val N.val ≫ e₀ ≫ fg
  have h₁ :
      L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val ≫ e' =
        (L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val) ≫ e' :=
    (Category.assoc _ _ _).symm
  have h₂ :
      (L.map (f.val ⊗ₘ g.val) ≫ δ M'.val N'.val) ≫ e' =
        (δ M.val N.val ≫ lfg) ≫ e' :=
    congrArg (fun k ↦ k ≫ e') hδ
  have h₃ :
      (δ M.val N.val ≫ lfg) ≫ e' =
        δ M.val N.val ≫ (lfg ≫ e') :=
    Category.assoc _ _ _
  have h₄ :
      δ M.val N.val ≫ (lfg ≫ e') =
        δ M.val N.val ≫ (e₀ ≫ fg) :=
    congrArg (fun k ↦ δ M.val N.val ≫ k) hTensorComp
  have h₅ :
      δ M.val N.val ≫ (e₀ ≫ fg) =
        δ M.val N.val ≫ e₀ ≫ fg :=
    (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Forming a pure tensor section commutes with morphisms in both module factors. -/
theorem tensorSection_map
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    (f ⊗ₘ g).val.app (.op U) (TensorSections.tensorSection M N U x y) =
      TensorSections.tensorSection M' N' U
        (f.val.app (.op U) x) (g.val.app (.op U) y) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let t : (M.val ⊗ N.val).obj (.op U) := x ⊗ₜ y
  let t' : (M'.val ⊗ N'.val).obj (.op U) :=
    f.val.app (.op U) x ⊗ₜ g.val.app (.op U) y
  let q := adj.unit.app (M.val ⊗ N.val)
  let q' := adj.unit.app (M'.val ⊗ N'.val)
  let a := q.app (.op U) t
  let a' := q'.app (.op U) t'
  have ht : (f.val ⊗ₘ g.val).app (.op U) t = t' := by
    rfl
  have hunit := adj.unit_naturality (f.val ⊗ₘ g.val)
  change adj.unit.app (M.val ⊗ N.val) ≫
      (L.map (f.val ⊗ₘ g.val)).val =
    (f.val ⊗ₘ g.val) ≫ adj.unit.app (M'.val ⊗ N'.val) at hunit
  have hunitU := congrArg (fun k ↦ k.app (.op U)) hunit
  have hunitApply := ConcreteCategory.congr_hom hunitU t
  conv_lhs at hunitApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hunitApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hLa : (L.map (f.val ⊗ₘ g.val)).val.app (.op U) a = a' := by
    dsimp only [a, a', q, q']
    have hright := congrArg
      (fun b ↦ (adj.unit.app (M'.val ⊗ N'.val)).app (.op U) b) ht
    exact hunitApply.trans hright
  have hk := monoidalTensorObjIso_inv_natural f g
  have hkU := congrArg (fun k ↦ k.val.app (.op U)) hk
  have hkApply := ConcreteCategory.congr_hom hkU a
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hkApply
  change (f ⊗ₘ g).val.app (.op U)
      ((TensorSections.monoidalTensorObjIso M N).inv.val.app (.op U) a) =
    (TensorSections.monoidalTensorObjIso M' N').inv.val.app (.op U) a'
  exact hkApply.symm.trans
    (congrArg
      (fun b ↦ (TensorSections.monoidalTensorObjIso M' N').inv.val.app (.op U) b) hLa)

section TensorMuSections

universe u₁ u₂ v₁ v₂

noncomputable local instance (X : Scheme.{u}) :
    SymmetricCategory (SheafOfModules X.ringCatSheaf) := by
  change SymmetricCategory X.Modules
  exact Projective.Monoidal.Scheme.Modules.symmetricCategory X

noncomputable local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).Braided :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (W := OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
    (Iso.refl _)).Braided)

theorem tensorMu_delta
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] (W X Y Z : C) :
    Functor.OplaxMonoidal.δ F (W ⊗ X) (Y ⊗ Z) ≫
        (Functor.OplaxMonoidal.δ F W X ⊗ₘ
          Functor.OplaxMonoidal.δ F Y Z) ≫
        tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) =
      F.map (tensorμ W X Y Z) ≫
        Functor.OplaxMonoidal.δ F (W ⊗ Y) (X ⊗ Z) ≫
        (Functor.OplaxMonoidal.δ F W Y ⊗ₘ
          Functor.OplaxMonoidal.δ F X Z) := by
  let s :=
    (Functor.LaxMonoidal.μ F W X ⊗ₘ Functor.LaxMonoidal.μ F Y Z) ≫
      Functor.LaxMonoidal.μ F (W ⊗ X) (Y ⊗ Z)
  apply (cancel_epi s).1
  have hμ := tensorμ_comp_μ_tensorHom_μ_comp_μ F W X Y Z
  have hsmap :
      s ≫ F.map (tensorμ W X Y Z) =
        tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) ≫
          (Functor.LaxMonoidal.μ F W Y ⊗ₘ
            Functor.LaxMonoidal.μ F X Z) ≫
          Functor.LaxMonoidal.μ F (W ⊗ Y) (X ⊗ Z) := by
    simpa only [s, Category.assoc] using hμ.symm
  calc
    s ≫ Functor.OplaxMonoidal.δ F (W ⊗ X) (Y ⊗ Z) ≫
          (Functor.OplaxMonoidal.δ F W X ⊗ₘ
            Functor.OplaxMonoidal.δ F Y Z) ≫
          tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) =
        tensorμ (F.obj W) (F.obj X) (F.obj Y) (F.obj Z) := by
      simp [s, Category.assoc]
    _ = s ≫ F.map (tensorμ W X Y Z) ≫
          Functor.OplaxMonoidal.δ F (W ⊗ Y) (X ⊗ Z) ≫
          (Functor.OplaxMonoidal.δ F W Y ⊗ₘ
            Functor.OplaxMonoidal.δ F X Z) := by
      rw [← Category.assoc]
      rw [hsmap]
      simp [Category.assoc]

theorem sheafification_delta_nested_tmul
    {X : Scheme.{u}} (A B C D : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (.op U)) (y : B.obj (.op U))
    (z : C.obj (.op U)) (w : D.obj (.op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let tAB : (A ⊗ B).obj (.op U) := x ⊗ₜ y
    let tCD : (C ⊗ D).obj (.op U) := z ⊗ₜ w
    ((Functor.OplaxMonoidal.δ L A B ⊗ₘ
        Functor.OplaxMonoidal.δ L C D).val.app (.op U))
      ((Functor.OplaxMonoidal.δ L (A ⊗ B) (C ⊗ D)).val.app (.op U)
        ((adj.unit.app ((A ⊗ B) ⊗ (C ⊗ D))).app (.op U)
          (tAB ⊗ₜ tCD))) =
      TensorSections.tensorSection (L.obj A ⊗ L.obj B) (L.obj C ⊗ L.obj D) U
        (TensorSections.tensorSection (L.obj A) (L.obj B) U
          ((adj.unit.app A).app (.op U) x)
          ((adj.unit.app B).app (.op U) y))
        (TensorSections.tensorSection (L.obj C) (L.obj D) U
          ((adj.unit.app C).app (.op U) z)
          ((adj.unit.app D).app (.op U) w)) := by
  dsimp only
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let tAB : (A ⊗ B).obj (.op U) := x ⊗ₜ y
  let tCD : (C ⊗ D).obj (.op U) := z ⊗ₜ w
  let dAB := Functor.OplaxMonoidal.δ L A B
  let dCD := Functor.OplaxMonoidal.δ L C D
  have hOuter := TensorSections.sheafification_δ_unit_tmul_eq_tensorSection
    (A ⊗ B) (C ⊗ D) U tAB tCD
  have hAB := TensorSections.sheafification_δ_unit_tmul_eq_tensorSection A B U x y
  have hCD := TensorSections.sheafification_δ_unit_tmul_eq_tensorSection C D U z w
  have hMap := tensorSection_map dAB dCD U
    ((adj.unit.app (A ⊗ B)).app (.op U) tAB)
    ((adj.unit.app (C ⊗ D)).app (.op U) tCD)
  have hInner := congrArg₂
    (TensorSections.tensorSection (L.obj A ⊗ L.obj B) (L.obj C ⊗ L.obj D) U)
      hAB hCD
  exact (congrArg (fun q ↦ (dAB ⊗ₘ dCD).val.app (.op U) q) hOuter).trans
    (hMap.trans hInner)

theorem sheafification_map_tensorMu_unit
    {X : Scheme.{u}} (A B C D : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (.op U)) (y : B.obj (.op U))
    (z : C.obj (.op U)) (w : D.obj (.op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let tSource : ((A ⊗ B) ⊗ (C ⊗ D)).obj (.op U) :=
      (show (A ⊗ B).obj (.op U) from x ⊗ₜ y) ⊗ₜ
        (show (C ⊗ D).obj (.op U) from z ⊗ₜ w)
    let tTarget : ((A ⊗ C) ⊗ (B ⊗ D)).obj (.op U) :=
      (show (A ⊗ C).obj (.op U) from x ⊗ₜ z) ⊗ₜ
        (show (B ⊗ D).obj (.op U) from y ⊗ₜ w)
    (L.map (tensorμ A B C D)).val.app (.op U)
        ((adj.unit.app ((A ⊗ B) ⊗ (C ⊗ D))).app (.op U) tSource) =
      (adj.unit.app ((A ⊗ C) ⊗ (B ⊗ D))).app (.op U) tTarget := by
  dsimp only
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let tSource : ((A ⊗ B) ⊗ (C ⊗ D)).obj (.op U) :=
    (show (A ⊗ B).obj (.op U) from x ⊗ₜ y) ⊗ₜ
      (show (C ⊗ D).obj (.op U) from z ⊗ₜ w)
  let tTarget : ((A ⊗ C) ⊗ (B ⊗ D)).obj (.op U) :=
    (show (A ⊗ C).obj (.op U) from x ⊗ₜ z) ⊗ₜ
      (show (B ⊗ D).obj (.op U) from y ⊗ₜ w)
  have ht : (tensorμ A B C D).app (.op U) tSource = tTarget := by
    rfl
  have hunit := adj.unit.naturality (tensorμ A B C D)
  have hunitU := congrArg (fun k ↦ k.app (.op U)) hunit
  have hunitApply := ConcreteCategory.congr_hom hunitU tSource
  conv_lhs at hunitApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hunitApply =>
    erw [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact hunitApply.symm.trans (congrArg
    (fun q ↦ (adj.unit.app ((A ⊗ C) ⊗ (B ⊗ D))).app (.op U) q) ht)

theorem sheafification_tensorMu_tensorSection
    {X : Scheme.{u}} (A B C D : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (.op U)) (y : B.obj (.op U))
    (z : C.obj (.op U)) (w : D.obj (.op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    (tensorμ (L.obj A) (L.obj B) (L.obj C) (L.obj D)).val.app (.op U)
        (TensorSections.tensorSection (L.obj A ⊗ L.obj B) (L.obj C ⊗ L.obj D) U
          (TensorSections.tensorSection (L.obj A) (L.obj B) U
            ((adj.unit.app A).app (.op U) x)
            ((adj.unit.app B).app (.op U) y))
          (TensorSections.tensorSection (L.obj C) (L.obj D) U
            ((adj.unit.app C).app (.op U) z)
            ((adj.unit.app D).app (.op U) w))) =
      TensorSections.tensorSection (L.obj A ⊗ L.obj C) (L.obj B ⊗ L.obj D) U
        (TensorSections.tensorSection (L.obj A) (L.obj C) U
          ((adj.unit.app A).app (.op U) x)
          ((adj.unit.app C).app (.op U) z))
        (TensorSections.tensorSection (L.obj B) (L.obj D) U
          ((adj.unit.app B).app (.op U) y)
          ((adj.unit.app D).app (.op U) w)) := by
  dsimp only
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let tSource : ((A ⊗ B) ⊗ (C ⊗ D)).obj (.op U) :=
    (show (A ⊗ B).obj (.op U) from x ⊗ₜ y) ⊗ₜ
      (show (C ⊗ D).obj (.op U) from z ⊗ₜ w)
  have hSource := sheafification_delta_nested_tmul A B C D U x y z w
  have hTarget := sheafification_delta_nested_tmul A C B D U x z y w
  have hMap := sheafification_map_tensorMu_unit A B C D U x y z w
  have hcoh := tensorMu_delta L A B C D
  have hcohApply := congrArg
    (fun k ↦ k.val.app (.op U)
      ((adj.unit.app ((A ⊗ B) ⊗ (C ⊗ D))).app (.op U) tSource)) hcoh
  conv_lhs at hcohApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at hcohApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_lhs at hcohApply =>
    rw [hSource]
  conv_rhs at hcohApply =>
    rw [hMap]
    rw [hTarget]
  exact hcohApply

end TensorMuSections

section TensorMuModuleSections

noncomputable local instance (X : Scheme.{u}) :
    SymmetricCategory (SheafOfModules X.ringCatSheaf) := by
  change SymmetricCategory X.Modules
  exact Projective.Monoidal.Scheme.Modules.symmetricCategory X

theorem sheafifyValIso_hom_unit_apply
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (Invertible.Scheme.Modules.sheafifyValIso M).hom.val.app (.op U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app M.val).app (.op U) x) = x := by
  rw [← PullbackTensorGeneral.Scheme.Modules.sheafifyValIso_inv_app_apply M U x]
  exact SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT
    (Invertible.Scheme.Modules.sheafifyValIso M) (.op U) x

theorem tensorSection_map_four
    {X : Scheme.{u}}
    {M₁ M₂ P₁ P₂ M₁' M₂' P₁' P₂' : X.Modules}
    (f₁ : M₁ ⟶ M₁') (f₂ : M₂ ⟶ M₂')
    (g₁ : P₁ ⟶ P₁') (g₂ : P₂ ⟶ P₂') (U : X.Opens)
    (x₁ : Γ(M₁, U)) (x₂ : Γ(M₂, U))
    (y₁ : Γ(P₁, U)) (y₂ : Γ(P₂, U)) :
    (((f₁ ⊗ₘ f₂) ⊗ₘ (g₁ ⊗ₘ g₂)).val.app (.op U))
        (TensorSections.tensorSection (M₁ ⊗ M₂) (P₁ ⊗ P₂) U
          (TensorSections.tensorSection M₁ M₂ U x₁ x₂)
          (TensorSections.tensorSection P₁ P₂ U y₁ y₂)) =
      TensorSections.tensorSection (M₁' ⊗ M₂') (P₁' ⊗ P₂') U
        (TensorSections.tensorSection M₁' M₂' U
          (f₁.val.app (.op U) x₁) (f₂.val.app (.op U) x₂))
        (TensorSections.tensorSection P₁' P₂' U
          (g₁.val.app (.op U) y₁) (g₂.val.app (.op U) y₂)) := by
  rw [tensorSection_map]
  rw [tensorSection_map, tensorSection_map]

noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules := by
  change SymmetricCategory (SheafOfModules X.ringCatSheaf)
  infer_instance

/-- Interchanging the middle factors of nested pure tensor sections acts
factorwise over every open. -/
theorem tensorMu_tensorSection
    {X : Scheme.{u}} (L₁ L₂ P₁ P₂ : X.Modules) (U : X.Opens)
    (x₁ : Γ(L₁, U)) (x₂ : Γ(L₂, U))
    (y₁ : Γ(P₁, U)) (y₂ : Γ(P₂, U)) :
    (tensorμ L₁ L₂ P₁ P₂).val.app (.op U)
        (TensorSections.tensorSection (L₁ ⊗ L₂) (P₁ ⊗ P₂) U
          (TensorSections.tensorSection L₁ L₂ U x₁ x₂)
          (TensorSections.tensorSection P₁ P₂ U y₁ y₂)) =
      TensorSections.tensorSection (L₁ ⊗ P₁) (L₂ ⊗ P₂) U
        (TensorSections.tensorSection L₁ P₁ U x₁ y₁)
        (TensorSections.tensorSection L₂ P₂ U x₂ y₂) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let c₁ := Invertible.Scheme.Modules.sheafifyValIso L₁
  let c₂ := Invertible.Scheme.Modules.sheafifyValIso L₂
  let d₁ := Invertible.Scheme.Modules.sheafifyValIso P₁
  let d₂ := Invertible.Scheme.Modules.sheafifyValIso P₂
  let u₁ := (adj.unit.app L₁.val).app (.op U) x₁
  let u₂ := (adj.unit.app L₂.val).app (.op U) x₂
  let v₁ := (adj.unit.app P₁.val).app (.op U) y₁
  let v₂ := (adj.unit.app P₂.val).app (.op U) y₂
  let qSource :=
    TensorSections.tensorSection (L.obj L₁.val ⊗ L.obj L₂.val)
      (L.obj P₁.val ⊗ L.obj P₂.val) U
      (TensorSections.tensorSection (L.obj L₁.val) (L.obj L₂.val) U u₁ u₂)
      (TensorSections.tensorSection (L.obj P₁.val) (L.obj P₂.val) U v₁ v₂)
  let qTarget :=
    TensorSections.tensorSection (L.obj L₁.val ⊗ L.obj P₁.val)
      (L.obj L₂.val ⊗ L.obj P₂.val) U
      (TensorSections.tensorSection (L.obj L₁.val) (L.obj P₁.val) U u₁ v₁)
      (TensorSections.tensorSection (L.obj L₂.val) (L.obj P₂.val) U u₂ v₂)
  let sourceMap := (c₁.hom ⊗ₘ c₂.hom) ⊗ₘ (d₁.hom ⊗ₘ d₂.hom)
  let targetMap := (c₁.hom ⊗ₘ d₁.hom) ⊗ₘ (c₂.hom ⊗ₘ d₂.hom)
  have hu₁ := sheafifyValIso_hom_unit_apply L₁ U x₁
  have hu₂ := sheafifyValIso_hom_unit_apply L₂ U x₂
  have hv₁ := sheafifyValIso_hom_unit_apply P₁ U y₁
  have hv₂ := sheafifyValIso_hom_unit_apply P₂ U y₂
  change c₁.hom.val.app (.op U) u₁ = x₁ at hu₁
  change c₂.hom.val.app (.op U) u₂ = x₂ at hu₂
  change d₁.hom.val.app (.op U) v₁ = y₁ at hv₁
  change d₂.hom.val.app (.op U) v₂ = y₂ at hv₂
  have hSource := tensorSection_map_four c₁.hom c₂.hom d₁.hom d₂.hom
    U u₁ u₂ v₁ v₂
  change sourceMap.val.app (.op U) qSource = _ at hSource
  rw [hu₁, hu₂, hv₁, hv₂] at hSource
  have hTarget := tensorSection_map_four c₁.hom d₁.hom c₂.hom d₂.hom
    U u₁ v₁ u₂ v₂
  change targetMap.val.app (.op U) qTarget = _ at hTarget
  rw [hu₁, hu₂, hv₁, hv₂] at hTarget
  have hSheaf := sheafification_tensorMu_tensorSection
    L₁.val L₂.val P₁.val P₂.val U x₁ x₂ y₁ y₂
  change
    (tensorμ (L.obj L₁.val) (L.obj L₂.val)
      (L.obj P₁.val) (L.obj P₂.val)).val.app (.op U) qSource = qTarget at hSheaf
  have hnatural := tensorμ_natural c₁.hom c₂.hom d₁.hom d₂.hom
  have hnaturalU := congrArg (fun k ↦ k.val.app (.op U)) hnatural
  have hnaturalApply := ConcreteCategory.congr_hom hnaturalU qSource
  conv_lhs at hnaturalApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at hnaturalApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  have hStart := congrArg
    (fun q ↦ (tensorμ L₁ L₂ P₁ P₂).val.app (.op U) q) hSource.symm
  have hMiddle := congrArg (fun q ↦ targetMap.val.app (.op U) q) hSheaf
  exact hStart.trans (hnaturalApply.trans (hMiddle.trans hTarget))

end TensorMuModuleSections

theorem poleTensorTopSection_map
    {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N')
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    (f ⊗ₘ g).val.app (.op ⊤) (poleTensorTopSection M N x y) =
      poleTensorTopSection M' N'
        (f.val.app (.op ⊤) x) (g.val.app (.op ⊤) y) :=
  tensorSection_map f g ⊤ x y

theorem monoidalTensorObjIso_unit_comp_unitObjTensorIso
    (X : Scheme.{u}) :
    (TensorSections.monoidalTensorObjIso (Invertible.Scheme.Modules.unitObj X)
          (Invertible.Scheme.Modules.unitObj X)).inv ≫
        (TensorSections.unitObjTensorIso X).hom =
      (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
          (λ_ (Invertible.Scheme.Modules.unitObj X).val).hom ≫
        (Invertible.Scheme.Modules.sheafifyValIso
          (Invertible.Scheme.Modules.unitObj X)).hom := by
  let : (OfModulesMonoidal.PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @OfModulesMonoidal.PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  let : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let c := TensorSections.monoidalUnitObjIso X
  have hcc :
      (c.hom ⊗ₘ c.hom) ≫ (c.inv ⊗ₘ c.inv) =
        𝟙 _ := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [c.hom_inv_id]
    rw [MonoidalCategory.tensorHom_id]
    rw [MonoidalCategory.id_whiskerRight]
  let t := (λ_ (𝟙_ X.Modules)).hom ≫ c.hom
  have hcct :
      (c.hom ⊗ₘ c.hom) ≫ (c.inv ⊗ₘ c.inv) ≫ t = t := by
    rw [← Category.assoc, hcc, Category.id_comp]
  have hcancel :
      (TensorSections.monoidalTensorObjIso (Invertible.Scheme.Modules.unitObj X)
            (Invertible.Scheme.Modules.unitObj X)).inv ≫
          (TensorSections.unitObjTensorIso X).hom =
        Functor.OplaxMonoidal.δ F
            (Invertible.Scheme.Modules.unitObj X).val
            (Invertible.Scheme.Modules.unitObj X).val ≫
          (λ_ (𝟙_ X.Modules)).hom ≫ c.hom := by
    change
      (Localization.Monoidal.μ
          (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
          (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
          (Iso.refl _) (Invertible.Scheme.Modules.unitObj X).val
            (Invertible.Scheme.Modules.unitObj X).val).inv ≫
        (c.hom ⊗ₘ c.hom) ≫
        (c.inv ⊗ₘ c.inv) ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ c.hom =
      Functor.OplaxMonoidal.δ F
          (Invertible.Scheme.Modules.unitObj X).val
          (Invertible.Scheme.Modules.unitObj X).val ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ c.hom
    let d :=
      (Localization.Monoidal.μ
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
        (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
        (Iso.refl _) (Invertible.Scheme.Modules.unitObj X).val
          (Invertible.Scheme.Modules.unitObj X).val).inv
    change d ≫ (c.hom ⊗ₘ c.hom) ≫ (c.inv ⊗ₘ c.inv) ≫ t = d ≫ t
    exact congrArg (fun k ↦ d ≫ k) hcct
  rw [hcancel]
  change
    Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules)
          (𝟙_ X.PresheafOfModules) ≫
        (λ_ (F.obj (𝟙_ X.PresheafOfModules))).hom ≫ c.hom =
      F.map (λ_ (𝟙_ X.PresheafOfModules)).hom ≫ c.hom
  have heta : Functor.OplaxMonoidal.η F = 𝟙 _ := by
    rfl
  have hid :
      𝟙 (F.obj (𝟙_ X.PresheafOfModules)) ▷
          F.obj (𝟙_ X.PresheafOfModules) = 𝟙 _ :=
    MonoidalCategory.id_whiskerRight _ _
  have hunit := Functor.OplaxMonoidal.left_unitality_hom_assoc F
    (𝟙_ X.PresheafOfModules) c.hom
  rw [heta] at hunit
  let s := (λ_ (F.obj (𝟙_ X.PresheafOfModules))).hom ≫ c.hom
  have hidt :
      (𝟙 (F.obj (𝟙_ X.PresheafOfModules)) ▷
          F.obj (𝟙_ X.PresheafOfModules)) ≫ s = s :=
    (congrArg (fun k ↦ k ≫ s) hid).trans (Category.id_comp s)
  have hpre := congrArg
    (fun k ↦ Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules)
      (𝟙_ X.PresheafOfModules) ≫ k) hidt
  exact hpre.symm.trans hunit

/-- Under the canonical tensor-unit identification, the pure tensor of two structure-sheaf
sections is their product. -/
theorem unitObjTensorIso_hom_tensorSection (X : Scheme.{u})
    (U : X.Opens) (a b : Γ(X, U)) :
    (TensorSections.unitObjTensorIso X).hom.val.app (.op U)
      (TensorSections.tensorSection _ _ U
        (show Γ(Invertible.Scheme.Modules.unitObj X, U) from a)
        (show Γ(Invertible.Scheme.Modules.unitObj X, U) from b)) =
      a * b := by
  let A := Invertible.Scheme.Modules.unitObj X
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let c := TensorSections.monoidalUnitObjIso X
  let q₀ : (A.val ⊗ A.val).obj (.op U) :=
    (show Γ(A, U) from a) ⊗ₜ
      (show Γ(A, U) from b)
  let uq := (adj.unit.app (A.val ⊗ A.val)).app
    (.op U) q₀
  have hmor := monoidalTensorObjIso_unit_comp_unitObjTensorIso X
  have hmorU := congrArg (fun k ↦ k.val.app (.op U)) hmor
  have hmorApply := ConcreteCategory.congr_hom hmorU uq
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hmorApply
  change (TensorSections.unitObjTensorIso X).hom.val.app (.op U)
      ((TensorSections.monoidalTensorObjIso A A).inv.val.app (.op U) uq) = _
  rw [hmorApply]
  let f := (λ_ A.val).hom
  have hnat := adj.unit_naturality f
  have htri := adj.right_triangle_components A
  change adj.unit.app (A.val ⊗ A.val) ≫ (L.map f).val =
    f ≫ adj.unit.app A.val at hnat
  change adj.unit.app A.val ≫ c.hom.val = 𝟙 A.val at htri
  have hpresheaf :
      adj.unit.app (A.val ⊗ A.val) ≫ (L.map f).val ≫ c.hom.val = f := by
    have hnatp :
        (adj.unit.app (A.val ⊗ A.val) ≫ (L.map f).val) ≫ c.hom.val =
          (f ≫ adj.unit.app A.val) ≫ c.hom.val :=
      congrArg (fun k ↦ k ≫ c.hom.val) hnat
    have htrip : f ≫ (adj.unit.app A.val ≫ c.hom.val) = f ≫ 𝟙 A.val :=
      congrArg (fun k ↦ f ≫ k) htri
    exact (Category.assoc _ _ _).symm |>.trans <|
      hnatp.trans <| (Category.assoc _ _ _).trans <|
        htrip.trans (Category.comp_id f)
  have hpresheafU := congrArg (fun k ↦ k.app (.op U)) hpresheaf
  have hpresheafApply := ConcreteCategory.congr_hom hpresheafU q₀
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hpresheafApply
  have hleft : ((λ_ A.val).hom.app (.op U)) q₀ = a * b := by
    have happ := PresheafOfModulesOfCommRing.leftUnitor_hom_app A.val (.op U)
    have heval := ConcreteCategory.congr_hom happ q₀
    have hmodule :
        ((λ_ (ModuleCat.of (X.sheaf.obj.obj (.op U))
          (X.sheaf.obj.obj (.op U)))).hom)
            (a ⊗ₜ b) = a • b :=
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply
        (R := X.sheaf.obj.obj (.op U))
        (M := ModuleCat.of (X.sheaf.obj.obj (.op U))
          (X.sheaf.obj.obj (.op U)))
        (show X.sheaf.obj.obj (.op U) from a)
        (show X.sheaf.obj.obj (.op U) from b)
    have hsmul : a • b = a * b := by
      rfl
    exact heval.trans (hmodule.trans hsmul)
  dsimp only [uq]
  exact hpresheafApply.trans hleft

theorem unitObjTensorIso_hom_tensorSection_top (X : Scheme.{u})
    (a b : Γ(X, (⊤ : X.Opens))) :
    (TensorSections.unitObjTensorIso X).hom.val.app (.op (⊤ : X.Opens))
      (TensorSections.tensorSection _ _ ⊤
        (show Γ(Invertible.Scheme.Modules.unitObj X, (⊤ : X.Opens)) from a)
        (show Γ(Invertible.Scheme.Modules.unitObj X, (⊤ : X.Opens)) from b)) =
      a * b :=
  unitObjTensorIso_hom_tensorSection X ⊤ a b

theorem unitObjTensorIso_inv_apply_one (X : Scheme.{u}) :
    (TensorSections.unitObjTensorIso X).inv.val.app (.op ⊤)
        (show X.presheaf.obj (.op ⊤) from 1) =
      poleTensorTopSection
        (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X)
        (show Γ(Invertible.Scheme.Modules.unitObj X, (⊤ : X.Opens)) from
          (show X.presheaf.obj (.op ⊤) from 1))
        (show Γ(Invertible.Scheme.Modules.unitObj X, (⊤ : X.Opens)) from
          (show X.presheaf.obj (.op ⊤) from 1)) := by
  let e := TensorSections.unitObjTensorIso X
  let q := poleTensorTopSection
    (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X)
    (show Γ(Invertible.Scheme.Modules.unitObj X, (⊤ : X.Opens)) from
      (show X.presheaf.obj (.op ⊤) from 1))
    (show Γ(Invertible.Scheme.Modules.unitObj X, (⊤ : X.Opens)) from
      (show X.presheaf.obj (.op ⊤) from 1))
  have hmul : e.hom.val.app (.op ⊤) q =
      (show X.presheaf.obj (.op ⊤) from 1) := by
    dsimp only [e, q, poleTensorTopSection]
    simpa only [one_mul] using
      unitObjTensorIso_hom_tensorSection_top X
        (show Γ(X, (⊤ : X.Opens)) from 1)
        (show Γ(X, (⊤ : X.Opens)) from 1)
  have hcomp := congrArg (fun k ↦ k.val.app (.op (⊤ : X.Opens)))
    e.hom_inv_id
  have hcompApply := ConcreteCategory.congr_hom hcomp q
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hcompApply
  have hcancel := congrArg (fun a ↦ e.inv.val.app (.op ⊤) a) hmul
  exact hcancel.symm.trans hcompApply

theorem poleTopSectionHom_tensorTopSection
    {X : Scheme.{u}} (M N : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    poleTopSectionHom (M ⊗ N) (poleTensorTopSection M N x y) =
      (TensorSections.unitObjTensorIso X).inv ≫
        (poleTopSectionHom M x ⊗ₘ poleTopSectionHom N y) := by
  apply poleUnitObj_hom_ext_top
  rw [poleTopSectionHom_app_top_apply_one]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [unitObjTensorIso_inv_apply_one]
  rw [poleTensorTopSection_map]
  exact congrArg₂ (fun a b ↦ poleTensorTopSection M N a b)
    (poleTopSectionHom_app_top_apply_one M x).symm
    (poleTopSectionHom_app_top_apply_one N y).symm

/-- The unit morphism associated to a pure tensor of global sections is the
tensor of the associated unit morphisms, precomposed with the canonical
inverse multiplication of the structure module. -/
theorem topSectionHom_tensorSection
    {X : Scheme.{u}} (M N : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    SectionIdentities.Scheme.Modules.topSectionHom (M ⊗ N) (TensorSections.tensorSection M N ⊤ x y) =
      (TensorSections.unitObjTensorIso X).inv ≫
        (SectionIdentities.Scheme.Modules.topSectionHom M x ⊗ₘ
          SectionIdentities.Scheme.Modules.topSectionHom N y) := by
  simpa only [SectionIdentities.Scheme.Modules.topSectionHom, poleTopSectionHom,
    poleTensorTopSection] using
    poleTopSectionHom_tensorTopSection M N x y

section SectionContraction

noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Projective.Monoidal.Scheme.Modules.symmetricCategory X

/-- Contract a global section of `M ⊗ P` against a pairing `L ⊗ P ⟶ 𝒪_X`
to obtain a morphism `L ⟶ M`. -/
noncomputable def sectionContractionHom {X : Scheme.{u}}
    (L M P : X.Modules) (pairing : L ⊗ P ⟶ Invertible.Scheme.Modules.unitObj X)
    (q : Γ(M ⊗ P, (⊤ : X.Opens))) : L ⟶ M :=
  (ρ_ L).inv ≫
    L ◁ ((TensorSections.monoidalUnitObjIso X).hom ≫
      SectionIdentities.Scheme.Modules.topSectionHom (M ⊗ P) q) ≫
    (α_ L M P).inv ≫
    (β_ L M).hom ▷ P ≫
    (α_ M L P).hom ≫
    M ◁ pairing ≫
    M ◁ (TensorSections.monoidalUnitObjIso X).inv ≫
    (ρ_ M).hom

theorem sectionContraction_scalarSlide {X : Scheme.{u}}
    (L M : X.Modules) (a : 𝟙_ X.Modules ⟶ M)
    (f : L ⟶ 𝟙_ X.Modules) :
    L ◁ a ≫ (β_ L M).hom ≫ M ◁ f ≫ (ρ_ M).hom =
      (ρ_ L).hom ≫ f ≫ a := by
  simp [Category.assoc]
  slice_lhs 2 3 => rw [← tensorHom_def]
  slice_lhs 2 2 => rw [tensorHom_def']
  simp [Category.assoc, ← unitors_equal]

theorem sectionContraction_assocWhisker {X : Scheme.{u}}
    (L M P : X.Modules) (b : 𝟙_ X.Modules ⟶ P) :
    (α_ L M (𝟙_ X.Modules)).hom ≫
        L ◁ M ◁ b ≫
        (α_ L M P).inv =
      (L ⊗ M) ◁ b := by
  monoidal

theorem sectionContraction_splitTensorStart {X : Scheme.{u}}
    (L M P : X.Modules)
    (a : 𝟙_ X.Modules ⟶ M) (b : 𝟙_ X.Modules ⟶ P) :
    L ◁ (λ_ (𝟙_ X.Modules)).inv ≫
        L ◁ (a ⊗ₘ b) =
      L ◁ a ≫
        (ρ_ (L ⊗ M)).inv ≫
        (α_ L M (𝟙_ X.Modules)).hom ≫
        L ◁ M ◁ b := by
  simp [tensorHom_def, Category.assoc]

theorem sectionContraction_gatherRight {X : Scheme.{u}}
    (L M P : X.Modules) (b : 𝟙_ X.Modules ⟶ P)
    (e : L ⊗ P ⟶ 𝟙_ X.Modules) :
    (ρ_ (L ⊗ M)).inv ≫
        (α_ L M (𝟙_ X.Modules)).hom ≫
        L ◁ M ◁ b ≫
        (α_ L M P).inv ≫
        (β_ L M).hom ▷ P ≫
        (α_ M L P).hom ≫
        M ◁ e =
      (β_ L M).hom ≫
        M ◁ ((ρ_ L).inv ≫ L ◁ b ≫ e) := by
  simp only [MonoidalCategory.whiskerLeft_comp]
  slice_lhs 2 4 =>
    rw [sectionContraction_assocWhisker (X := X) L M P b]
  slice_lhs 2 3 => rw [whisker_exchange]
  slice_lhs 1 2 => rw [← rightUnitor_inv_naturality]
  slice_lhs 3 4 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_rightUnitor_inv]
  simp only [Category.assoc]

theorem sectionContraction_pure {X : Scheme.{u}}
    (L M P : X.Modules)
    (a : 𝟙_ X.Modules ⟶ M) (b : 𝟙_ X.Modules ⟶ P)
    (e : L ⊗ P ⟶ 𝟙_ X.Modules) :
    L ◁ (λ_ (𝟙_ X.Modules)).inv ≫
        L ◁ (a ⊗ₘ b) ≫
        (α_ L M P).inv ≫
        (β_ L M).hom ▷ P ≫
        (α_ M L P).hom ≫
        M ◁ e ≫
        (ρ_ M).hom =
      L ◁ b ≫ e ≫ a := by
  calc
    _ = L ◁ a ≫ (β_ L M).hom ≫
        M ◁ ((ρ_ L).inv ≫ L ◁ b ≫ e) ≫ (ρ_ M).hom := by
      slice_lhs 1 2 =>
        rw [sectionContraction_splitTensorStart (X := X) L M P a b]
      slice_lhs 2 8 =>
        rw [sectionContraction_gatherRight (X := X) L M P b e]
      simp only [Category.assoc]
    _ = (ρ_ L).hom ≫ ((ρ_ L).inv ≫ L ◁ b ≫ e) ≫ a :=
      sectionContraction_scalarSlide (X := X) L M a
        ((ρ_ L).inv ≫ L ◁ b ≫ e)
    _ = _ := by simp

/-- Contracting a pure tensor evaluates its `P`-factor against the pairing and
then applies the section of `M`. -/
theorem sectionContractionHom_tensorSection {X : Scheme.{u}}
    (L M P : X.Modules) (pairing : L ⊗ P ⟶ Invertible.Scheme.Modules.unitObj X)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(P, (⊤ : X.Opens))) :
    sectionContractionHom L M P pairing (TensorSections.tensorSection M P ⊤ x y) =
      (ρ_ L).inv ≫
        L ◁ ((TensorSections.monoidalUnitObjIso X).hom ≫
          SectionIdentities.Scheme.Modules.topSectionHom P y) ≫
        pairing ≫ SectionIdentities.Scheme.Modules.topSectionHom M x := by
  rw [sectionContractionHom, topSectionHom_tensorSection]
  simp [TensorSections.unitObjTensorIso, Category.assoc]
  slice_lhs 6 7 => rw [← MonoidalCategory.whiskerLeft_comp]
  rw [sectionContraction_pure (X := X) L M P
    ((TensorSections.monoidalUnitObjIso X).hom ≫ SectionIdentities.Scheme.Modules.topSectionHom M x)
    ((TensorSections.monoidalUnitObjIso X).hom ≫ SectionIdentities.Scheme.Modules.topSectionHom P y)
    (pairing ≫ (TensorSections.monoidalUnitObjIso X).inv)]
  simp [Category.assoc]

end SectionContraction

/-- Evaluation against the sheaf dual, expressed using the localized monoidal tensor. -/
noncomputable def dualPairing {X : Scheme.{u}} (M : X.Modules) :
    M ⊗ Dual.Scheme.Modules.dualObj M ⟶ Invertible.Scheme.Modules.unitObj X :=
  (TensorSections.monoidalTensorObjIso M (Dual.Scheme.Modules.dualObj M)).hom ≫
    Evaluation.Scheme.Modules.ev M

/-- The localized dual pairing evaluates a pure tensor section pointwise. -/
theorem dualPairing_tensorSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (x : Γ(M, U))
    (φ : Γ(Dual.Scheme.Modules.dualObj M, U)) :
    (dualPairing M).val.app (.op U)
        (TensorSections.tensorSection M (Dual.Scheme.Modules.dualObj M) U x φ) =
      Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ x := by
  let D := Dual.Scheme.Modules.dualObj M
  let P := M.val ⊗ D.val
  let k := TensorSections.monoidalTensorObjIso M D
  let t : P.obj (.op U) := x ⊗ₜ φ
  let a : ((PresheafOfModules.sheafification
      (CategoryStruct.id X.ringCatSheaf.obj)).obj P).val.obj (.op U) :=
    ((PresheafOfModules.sheafificationAdjunction
      (CategoryStruct.id X.ringCatSheaf.obj)).unit.app P).app (.op U) t
  have hk := SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT k (.op U) a
  have hev := ((PresheafOfModules.sheafificationAdjunction
    (CategoryStruct.id X.ringCatSheaf.obj)).homEquiv
      P (Invertible.Scheme.Modules.unitObj X)).apply_symm_apply
        (Evaluation.Scheme.Modules.evPre M)
  change
    (PresheafOfModules.sheafificationAdjunction
        (CategoryStruct.id X.ringCatSheaf.obj)).unit.app P ≫
        (Evaluation.Scheme.Modules.ev M).val = Evaluation.Scheme.Modules.evPre M at hev
  have hevApp := congrArg (fun q => q.app (.op U)) hev
  have hevApply := ConcreteCategory.congr_hom hevApp t
  change (Evaluation.Scheme.Modules.ev M).val.app (.op U) a =
    (Evaluation.Scheme.Modules.evPre M).app (.op U) t at hevApply
  change (Evaluation.Scheme.Modules.ev M).val.app (.op U) a =
    Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ x at hevApply
  change (k.hom ≫ Evaluation.Scheme.Modules.ev M).val.app (.op U)
      (k.inv.val.app (.op U) a) = _
  erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [hk]
  exact hevApply

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

/-- A coefficient-one local frame evaluates to `1` against its coefficient-one
dual frame. -/
theorem dualPairing_overTrivializationSection_one
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (dualPairing M).val.app (.op U)
        (TensorSections.tensorSection M (Dual.Scheme.Modules.dualObj M) U
          (FrameSections.overTrivializationSection M U e 1)
          (FrameSections.overTrivializationSection (Dual.Scheme.Modules.dualObj M) U
            (Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U e) 1)) =
      (show Γ(X, U) from 1) := by
  let d := Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U e
  let x : Γ(M, U) := FrameSections.overTrivializationSection M U e 1
  let φ : Γ(Dual.Scheme.Modules.dualObj M, U) :=
    FrameSections.overTrivializationSection (Dual.Scheme.Modules.dualObj M) U d 1
  have hφ : φ = e.hom := by
    dsimp only [φ, FrameSections.overTrivializationSection, d]
    exact SectionIdentities.Scheme.Modules.dualOverIsoOfIso_inv_terminal_apply_oneT M U e
  rw [dualPairing_tensorSection]
  change Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ x = _
  rw [hφ]
  change e.hom.val.app (.op (Over.mk (𝟙 U)))
      (M.val.map (𝟙 U).op x) = _
  have hmap : M.val.map (𝟙 (.op U)) x = x := by
    exact Functor.map_id_apply M.val.presheaf (.op U) x
  rw [op_id, hmap]
  exact FrameSections.overTrivializationSection_coefficient M U e 1

section TensorPairing

noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Projective.Monoidal.Scheme.Modules.symmetricCategory X

/-- Pair two tensor products by interchanging the middle factors and pairing
the corresponding factors. -/
noncomputable def tensorPairing {X : Scheme.{u}}
    {L₁ L₂ P₁ P₂ : X.Modules}
    (e₁ : L₁ ⊗ P₁ ⟶ Invertible.Scheme.Modules.unitObj X)
    (e₂ : L₂ ⊗ P₂ ⟶ Invertible.Scheme.Modules.unitObj X) :
    (L₁ ⊗ L₂) ⊗ (P₁ ⊗ P₂) ⟶ Invertible.Scheme.Modules.unitObj X :=
  tensorμ L₁ L₂ P₁ P₂ ≫
    (e₁ ⊗ₘ e₂) ≫
    (TensorSections.unitObjTensorIso X).hom

/-- Pairing two nested pure tensor sections over an arbitrary open multiplies
the two factorwise pairing values. -/
theorem tensorPairing_tensorSection {X : Scheme.{u}}
    {L₁ L₂ P₁ P₂ : X.Modules}
    (e₁ : L₁ ⊗ P₁ ⟶ Invertible.Scheme.Modules.unitObj X)
    (e₂ : L₂ ⊗ P₂ ⟶ Invertible.Scheme.Modules.unitObj X)
    (U : X.Opens) (x₁ : Γ(L₁, U)) (x₂ : Γ(L₂, U))
    (y₁ : Γ(P₁, U)) (y₂ : Γ(P₂, U)) :
    (tensorPairing e₁ e₂).val.app (.op U)
        (TensorSections.tensorSection (L₁ ⊗ L₂) (P₁ ⊗ P₂) U
          (TensorSections.tensorSection L₁ L₂ U x₁ x₂)
          (TensorSections.tensorSection P₁ P₂ U y₁ y₂)) =
      (show Γ(X, U) from
        e₁.val.app (.op U) (TensorSections.tensorSection L₁ P₁ U x₁ y₁)) *
        (show Γ(X, U) from
          e₂.val.app (.op U) (TensorSections.tensorSection L₂ P₂ U x₂ y₂)) := by
  change
    ((tensorμ L₁ L₂ P₁ P₂ ≫ (e₁ ⊗ₘ e₂) ≫
      (TensorSections.unitObjTensorIso X).hom).val.app (.op U)) _ = _
  conv_lhs =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  rw [tensorMu_tensorSection]
  rw [tensorSection_map]
  exact unitObjTensorIso_hom_tensorSection X U
    (e₁.val.app (.op U) (TensorSections.tensorSection L₁ P₁ U x₁ y₁))
    (e₂.val.app (.op U) (TensorSections.tensorSection L₂ P₂ U x₂ y₂))

end TensorPairing

theorem poleTopSectionHom_comp
    {X : Scheme.{u}} {M N : X.Modules} (x : Γ(M, (⊤ : X.Opens)))
    (f : M ⟶ N) :
    poleTopSectionHom M x ≫ f =
      poleTopSectionHom N (f.val.app (.op ⊤) x) := by
  apply poleUnitObj_hom_ext_top
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  calc
    f.val.app (.op ⊤)
        ((poleTopSectionHom M x).val.app (.op ⊤)
          (show X.presheaf.obj (.op ⊤) from 1)) =
      f.val.app (.op ⊤) x := congrArg
        (fun q ↦ f.val.app (.op ⊤) q)
        (poleTopSectionHom_app_top_apply_one M x)
    _ = (poleTopSectionHom N (f.val.app (.op ⊤) x)).val.app (.op ⊤)
        (show X.presheaf.obj (.op ⊤) from 1) :=
      (poleTopSectionHom_app_top_apply_one N
        (f.val.app (.op ⊤) x)).symm

/-- Postcomposing the morphism associated to a top-open section applies the
postcomposed morphism to that section. -/
theorem topSectionHom_comp
    {X : Scheme.{u}} {M N : X.Modules} (x : Γ(M, (⊤ : X.Opens)))
    (f : M ⟶ N) :
    SectionIdentities.Scheme.Modules.topSectionHom M x ≫ f =
      SectionIdentities.Scheme.Modules.topSectionHom N (f.val.app (.op ⊤) x) := by
  simpa only [SectionIdentities.Scheme.Modules.topSectionHom, poleTopSectionHom] using
    poleTopSectionHom_comp x f

section TensorPairingSections

noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Projective.Monoidal.Scheme.Modules.symmetricCategory X

theorem tensorPairing_unit_tensorμ (X : Scheme.{u}) :
    let O := Invertible.Scheme.Modules.unitObj X
    let u := TensorSections.unitObjTensorIso X
    u.inv ≫ (u.inv ⊗ₘ u.inv) ≫ tensorμ O O O O =
      u.inv ≫ (u.inv ⊗ₘ u.inv) := by
  let O := Invertible.Scheme.Modules.unitObj X
  let u := TensorSections.unitObjTensorIso X
  let c := TensorSections.monoidalUnitObjIso X
  let l := (λ_ (𝟙_ X.Modules)).inv
  have hsource :
      ((l ≫ (c.hom ⊗ₘ c.hom)) ⊗ₘ (l ≫ (c.hom ⊗ₘ c.hom))) =
        (l ⊗ₘ l) ≫ ((c.hom ⊗ₘ c.hom) ⊗ₘ (c.hom ⊗ₘ c.hom)) :=
    (tensorHom_comp_tensorHom l l (c.hom ⊗ₘ c.hom)
      (c.hom ⊗ₘ c.hom)).symm
  have hnatural := tensorμ_natural c.hom c.hom c.hom c.hom
  have hunit :
      (l ⊗ₘ l) ≫ tensorμ (𝟙_ X.Modules) (𝟙_ X.Modules)
          (𝟙_ X.Modules) (𝟙_ X.Modules) = l ⊗ₘ l := by
    dsimp only [l]
    simp only [tensorμ, braiding_tensorUnit_left]
    monoidal
  have hinner :
      ((l ≫ (c.hom ⊗ₘ c.hom)) ⊗ₘ (l ≫ (c.hom ⊗ₘ c.hom))) ≫
          tensorμ (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X)
            (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X) =
        ((l ≫ (c.hom ⊗ₘ c.hom)) ⊗ₘ
          (l ≫ (c.hom ⊗ₘ c.hom))) := by
    calc
      _ = (l ⊗ₘ l) ≫ ((c.hom ⊗ₘ c.hom) ⊗ₘ (c.hom ⊗ₘ c.hom)) ≫
            tensorμ (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X)
              (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X) := by
        rw [hsource]
        simp only [Category.assoc]
      _ = (l ⊗ₘ l) ≫
            tensorμ (𝟙_ X.Modules) (𝟙_ X.Modules)
              (𝟙_ X.Modules) (𝟙_ X.Modules) ≫
            ((c.hom ⊗ₘ c.hom) ⊗ₘ (c.hom ⊗ₘ c.hom)) := by
        simpa only [Category.assoc] using
          congrArg (fun k ↦ (l ⊗ₘ l) ≫ k) hnatural
      _ = (l ⊗ₘ l) ≫
            ((c.hom ⊗ₘ c.hom) ⊗ₘ (c.hom ⊗ₘ c.hom)) := by
        rw [reassoc_of% hunit]
      _ = _ := hsource.symm
  simpa [u, O, c, l, TensorSections.unitObjTensorIso, Category.assoc] using hinner

theorem tensorPairing_morphism {X : Scheme.{u}}
    {L₁ L₂ P₁ P₂ : X.Modules}
    (e₁ : L₁ ⊗ P₁ ⟶ Invertible.Scheme.Modules.unitObj X)
    (e₂ : L₂ ⊗ P₂ ⟶ Invertible.Scheme.Modules.unitObj X)
    (a₁ : Invertible.Scheme.Modules.unitObj X ⟶ L₁)
    (a₂ : Invertible.Scheme.Modules.unitObj X ⟶ L₂)
    (b₁ : Invertible.Scheme.Modules.unitObj X ⟶ P₁)
    (b₂ : Invertible.Scheme.Modules.unitObj X ⟶ P₂) :
    (TensorSections.unitObjTensorIso X).inv ≫
        (((TensorSections.unitObjTensorIso X).inv ≫ (a₁ ⊗ₘ a₂)) ⊗ₘ
          ((TensorSections.unitObjTensorIso X).inv ≫ (b₁ ⊗ₘ b₂))) ≫
        tensorPairing e₁ e₂ =
      (TensorSections.unitObjTensorIso X).inv ≫
        (((TensorSections.unitObjTensorIso X).inv ≫ (a₁ ⊗ₘ b₁) ≫ e₁) ⊗ₘ
          ((TensorSections.unitObjTensorIso X).inv ≫ (a₂ ⊗ₘ b₂) ≫ e₂)) ≫
        (TensorSections.unitObjTensorIso X).hom := by
  let O := Invertible.Scheme.Modules.unitObj X
  let u := TensorSections.unitObjTensorIso X
  have hsource :
      ((u.inv ≫ (a₁ ⊗ₘ a₂)) ⊗ₘ (u.inv ≫ (b₁ ⊗ₘ b₂))) =
        (u.inv ⊗ₘ u.inv) ≫ ((a₁ ⊗ₘ a₂) ⊗ₘ (b₁ ⊗ₘ b₂)) :=
    (tensorHom_comp_tensorHom u.inv u.inv (a₁ ⊗ₘ a₂) (b₁ ⊗ₘ b₂)).symm
  have hnatural := tensorμ_natural a₁ a₂ b₁ b₂
  have hunit :
      u.inv ≫ (u.inv ⊗ₘ u.inv) ≫ tensorμ O O O O =
        u.inv ≫ (u.inv ⊗ₘ u.inv) :=
    tensorPairing_unit_tensorμ X
  have htarget₀ :
      ((u.inv ≫ (a₁ ⊗ₘ b₁) ≫ e₁) ⊗ₘ
          (u.inv ≫ (a₂ ⊗ₘ b₂) ≫ e₂)) =
        (u.inv ⊗ₘ u.inv) ≫
          (((a₁ ⊗ₘ b₁) ≫ e₁) ⊗ₘ ((a₂ ⊗ₘ b₂) ≫ e₂)) :=
    (tensorHom_comp_tensorHom u.inv u.inv
      ((a₁ ⊗ₘ b₁) ≫ e₁) ((a₂ ⊗ₘ b₂) ≫ e₂)).symm
  have htarget₁ :
      (((a₁ ⊗ₘ b₁) ≫ e₁) ⊗ₘ ((a₂ ⊗ₘ b₂) ≫ e₂)) =
        ((a₁ ⊗ₘ b₁) ⊗ₘ (a₂ ⊗ₘ b₂)) ≫ (e₁ ⊗ₘ e₂) :=
    (tensorHom_comp_tensorHom (a₁ ⊗ₘ b₁) (a₂ ⊗ₘ b₂) e₁ e₂).symm
  simp only [tensorPairing]
  calc
    u.inv ≫
          ((u.inv ≫ (a₁ ⊗ₘ a₂)) ⊗ₘ (u.inv ≫ (b₁ ⊗ₘ b₂))) ≫
          tensorμ L₁ L₂ P₁ P₂ ≫ (e₁ ⊗ₘ e₂) ≫ u.hom =
        u.inv ≫ (u.inv ⊗ₘ u.inv) ≫
          ((a₁ ⊗ₘ a₂) ⊗ₘ (b₁ ⊗ₘ b₂)) ≫
          tensorμ L₁ L₂ P₁ P₂ ≫ (e₁ ⊗ₘ e₂) ≫ u.hom := by
      rw [hsource]
      simp only [Category.assoc]
    _ = u.inv ≫ (u.inv ⊗ₘ u.inv) ≫ tensorμ O O O O ≫
          ((a₁ ⊗ₘ b₁) ⊗ₘ (a₂ ⊗ₘ b₂)) ≫
          (e₁ ⊗ₘ e₂) ≫ u.hom := by
      rw [reassoc_of% hnatural]
    _ = u.inv ≫ (u.inv ⊗ₘ u.inv) ≫
          ((a₁ ⊗ₘ b₁) ⊗ₘ (a₂ ⊗ₘ b₂)) ≫
          (e₁ ⊗ₘ e₂) ≫ u.hom := by
      rw [reassoc_of% hunit]
    _ = u.inv ≫
          ((u.inv ≫ (a₁ ⊗ₘ b₁) ≫ e₁) ⊗ₘ
            (u.inv ≫ (a₂ ⊗ₘ b₂) ≫ e₂)) ≫ u.hom := by
      rw [htarget₀, htarget₁]
      simp only [Category.assoc]

/-- Pairing two nested pure tensor sections over the top open multiplies the
two factorwise pairing values. -/
theorem tensorPairing_tensorSection_top {X : Scheme.{u}}
    {L₁ L₂ P₁ P₂ : X.Modules}
    (e₁ : L₁ ⊗ P₁ ⟶ Invertible.Scheme.Modules.unitObj X)
    (e₂ : L₂ ⊗ P₂ ⟶ Invertible.Scheme.Modules.unitObj X)
    (x₁ : Γ(L₁, (⊤ : X.Opens))) (x₂ : Γ(L₂, (⊤ : X.Opens)))
    (y₁ : Γ(P₁, (⊤ : X.Opens))) (y₂ : Γ(P₂, (⊤ : X.Opens))) :
    (tensorPairing e₁ e₂).val.app (.op ⊤)
        (TensorSections.tensorSection (L₁ ⊗ L₂) (P₁ ⊗ P₂) ⊤
          (TensorSections.tensorSection L₁ L₂ ⊤ x₁ x₂)
          (TensorSections.tensorSection P₁ P₂ ⊤ y₁ y₂)) =
      (show Γ(X, (⊤ : X.Opens)) from
        e₁.val.app (.op ⊤) (TensorSections.tensorSection L₁ P₁ ⊤ x₁ y₁)) *
        (show Γ(X, (⊤ : X.Opens)) from
          e₂.val.app (.op ⊤) (TensorSections.tensorSection L₂ P₂ ⊤ x₂ y₂)) := by
  let u := TensorSections.unitObjTensorIso X
  let a₁ := SectionIdentities.Scheme.Modules.topSectionHom L₁ x₁
  let a₂ := SectionIdentities.Scheme.Modules.topSectionHom L₂ x₂
  let b₁ := SectionIdentities.Scheme.Modules.topSectionHom P₁ y₁
  let b₂ := SectionIdentities.Scheme.Modules.topSectionHom P₂ y₂
  let x := TensorSections.tensorSection L₁ L₂ ⊤ x₁ x₂
  let y := TensorSections.tensorSection P₁ P₂ ⊤ y₁ y₂
  let q := TensorSections.tensorSection (L₁ ⊗ L₂) (P₁ ⊗ P₂) ⊤ x y
  let z₁ := TensorSections.tensorSection L₁ P₁ ⊤ x₁ y₁
  let z₂ := TensorSections.tensorSection L₂ P₂ ⊤ x₂ y₂
  let r₁ : Γ(X, (⊤ : X.Opens)) := e₁.val.app (.op ⊤) z₁
  let r₂ : Γ(X, (⊤ : X.Opens)) := e₂.val.app (.op ⊤) z₂
  have hx : SectionIdentities.Scheme.Modules.topSectionHom (L₁ ⊗ L₂) x =
      u.inv ≫ (a₁ ⊗ₘ a₂) := by
    exact topSectionHom_tensorSection L₁ L₂ x₁ x₂
  have hy : SectionIdentities.Scheme.Modules.topSectionHom (P₁ ⊗ P₂) y =
      u.inv ≫ (b₁ ⊗ₘ b₂) := by
    exact topSectionHom_tensorSection P₁ P₂ y₁ y₂
  have hq : SectionIdentities.Scheme.Modules.topSectionHom ((L₁ ⊗ L₂) ⊗ (P₁ ⊗ P₂)) q =
      u.inv ≫
        (SectionIdentities.Scheme.Modules.topSectionHom (L₁ ⊗ L₂) x ⊗ₘ
          SectionIdentities.Scheme.Modules.topSectionHom (P₁ ⊗ P₂) y) := by
    exact topSectionHom_tensorSection (L₁ ⊗ L₂) (P₁ ⊗ P₂) x y
  have hz₁ : SectionIdentities.Scheme.Modules.topSectionHom (L₁ ⊗ P₁) z₁ =
      u.inv ≫ (a₁ ⊗ₘ b₁) := by
    exact topSectionHom_tensorSection L₁ P₁ x₁ y₁
  have hz₂ : SectionIdentities.Scheme.Modules.topSectionHom (L₂ ⊗ P₂) z₂ =
      u.inv ≫ (a₂ ⊗ₘ b₂) := by
    exact topSectionHom_tensorSection L₂ P₂ x₂ y₂
  have hr₁ : u.inv ≫ (a₁ ⊗ₘ b₁) ≫ e₁ =
      UnitScalar.unitEndomorphismOfTopSection r₁ := by
    calc
      _ = SectionIdentities.Scheme.Modules.topSectionHom (L₁ ⊗ P₁) z₁ ≫ e₁ := by
        rw [hz₁]
        simp only [Category.assoc]
      _ = SectionIdentities.Scheme.Modules.topSectionHom (Invertible.Scheme.Modules.unitObj X) r₁ :=
        topSectionHom_comp z₁ e₁
      _ = _ := rfl
  have hr₂ : u.inv ≫ (a₂ ⊗ₘ b₂) ≫ e₂ =
      UnitScalar.unitEndomorphismOfTopSection r₂ := by
    calc
      _ = SectionIdentities.Scheme.Modules.topSectionHom (L₂ ⊗ P₂) z₂ ≫ e₂ := by
        rw [hz₂]
        simp only [Category.assoc]
      _ = SectionIdentities.Scheme.Modules.topSectionHom (Invertible.Scheme.Modules.unitObj X) r₂ :=
        topSectionHom_comp z₂ e₂
      _ = _ := rfl
  have hpair :
      SectionIdentities.Scheme.Modules.topSectionHom ((L₁ ⊗ L₂) ⊗ (P₁ ⊗ P₂)) q ≫
          tensorPairing e₁ e₂ =
        UnitScalar.unitEndomorphismOfTopSection (r₁ * r₂) := by
    calc
      _ = u.inv ≫
          ((u.inv ≫ (a₁ ⊗ₘ a₂)) ⊗ₘ (u.inv ≫ (b₁ ⊗ₘ b₂))) ≫
            tensorPairing e₁ e₂ := by
        rw [hq, hx, hy]
        simp only [Category.assoc]
      _ = u.inv ≫
          ((u.inv ≫ (a₁ ⊗ₘ b₁) ≫ e₁) ⊗ₘ
            (u.inv ≫ (a₂ ⊗ₘ b₂) ≫ e₂)) ≫ u.hom :=
        tensorPairing_morphism e₁ e₂ a₁ a₂ b₁ b₂
      _ = u.inv ≫
          (UnitScalar.unitEndomorphismOfTopSection r₁ ⊗ₘ
            UnitScalar.unitEndomorphismOfTopSection r₂) ≫ u.hom := by
        rw [hr₁, hr₂]
      _ = _ := by
        rw [TensorSections.unitObjTensorIso_hom_comp_scalars]
        exact u.inv_hom_id_assoc _
  have hresult :
      SectionIdentities.Scheme.Modules.topSectionHom (Invertible.Scheme.Modules.unitObj X)
          ((tensorPairing e₁ e₂).val.app (.op ⊤) q) =
        SectionIdentities.Scheme.Modules.topSectionHom (Invertible.Scheme.Modules.unitObj X) (r₁ * r₂) := by
    calc
      _ = SectionIdentities.Scheme.Modules.topSectionHom ((L₁ ⊗ L₂) ⊗ (P₁ ⊗ P₂)) q ≫
          tensorPairing e₁ e₂ := (topSectionHom_comp q (tensorPairing e₁ e₂)).symm
      _ = UnitScalar.unitEndomorphismOfTopSection (r₁ * r₂) := hpair
      _ = _ := rfl
  have happ := congrArg
    (fun k ↦ k.val.app (.op (⊤ : X.Opens))
      (show X.presheaf.obj (.op ⊤) from 1)) hresult
  have hfinal : (tensorPairing e₁ e₂).val.app (.op ⊤) q = r₁ * r₂ :=
    (SectionIdentities.Scheme.Modules.topSectionHom_app_top_apply_one
      (Invertible.Scheme.Modules.unitObj X)
      ((tensorPairing e₁ e₂).val.app (.op ⊤) q)).symm.trans
        (happ.trans (SectionIdentities.Scheme.Modules.topSectionHom_app_top_apply_one
          (Invertible.Scheme.Modules.unitObj X) (r₁ * r₂)))
  dsimp only [q] at hfinal
  dsimp only [x, y] at hfinal
  dsimp only [r₁, r₂] at hfinal
  dsimp only [z₁, z₂] at hfinal
  exact hfinal

end TensorPairingSections

theorem poleTensor_restrict_monoidalUnitObjIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    let F := Scheme.Modules.restrictFunctor f
    letI : (Scheme.Modules.pullback f).Monoidal :=
      PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
    letI : F.Monoidal := Functor.Monoidal.transport
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
    F.map (TensorSections.monoidalUnitObjIso Y).hom ≫
        (Scheme.Modules.restrictUnitIso f).hom =
      Functor.OplaxMonoidal.η F ≫ (TensorSections.monoidalUnitObjIso X).hom := by
  let F := Scheme.Modules.restrictFunctor f
  let G := Scheme.Modules.pullback f
  let : G.Monoidal := PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback f).symm
  let R := Scheme.Modules.restrictFunctorIsoPullback f
  let q : F.obj (Invertible.Scheme.Modules.unitObj Y) ⟶ Invertible.Scheme.Modules.unitObj X :=
    (Scheme.Modules.restrictUnitIso f).hom
  let p : G.obj (Invertible.Scheme.Modules.unitObj Y) ⟶ Invertible.Scheme.Modules.unitObj X :=
    (Invertible.Scheme.Modules.pullbackUnitIso f).hom
  have hpull :
      (Functor.Monoidal.εIso G).inv ≫ (TensorSections.monoidalUnitObjIso X).hom =
        G.map (TensorSections.monoidalUnitObjIso Y).hom ≫ p := by
    have h := congrArg Iso.hom
      (PullbackUnitMonoidal.Scheme.Modules.pullback_monoidalUnitObjIso f)
    change (Functor.Monoidal.εIso G).inv ≫
        (TensorSections.monoidalUnitObjIso X).hom =
      G.map (TensorSections.monoidalUnitObjIso Y).hom ≫ p at h
    exact h
  have hrestrict :
      R.hom.app (Invertible.Scheme.Modules.unitObj Y) ≫ p = q := by
    have h := RestrictionUnit.restrictFunctorIsoPullback_inv_comp_restrictUnitIso f
    let eR := R.app (Invertible.Scheme.Modules.unitObj Y)
    have h' : eR.inv ≫ q = p := h
    calc
      eR.hom ≫ p = eR.hom ≫ (eR.inv ≫ q) :=
        congrArg (fun k ↦ eR.hom ≫ k) h'.symm
      _ = (eR.hom ≫ eR.inv) ≫ q := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ q := congrArg (fun k ↦ k ≫ q) eR.hom_inv_id
      _ = q := Category.id_comp q
  have hnat := R.hom.naturality (TensorSections.monoidalUnitObjIso Y).hom
  change F.map (TensorSections.monoidalUnitObjIso Y).hom ≫ q =
    R.hom.app (𝟙_ Y.Modules) ≫
      (Functor.Monoidal.εIso G).inv ≫ (TensorSections.monoidalUnitObjIso X).hom
  rw [hpull]
  rw [← Category.assoc]
  rw [← hnat]
  rw [Category.assoc]
  rw [hrestrict]

theorem poleTensor_restrict_monoidalUnitObjIso_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    let F := Scheme.Modules.restrictFunctor f
    letI : (Scheme.Modules.pullback f).Monoidal :=
      PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
    letI : F.Monoidal := Functor.Monoidal.transport
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
    (Scheme.Modules.restrictUnitIso f).inv ≫
        F.map (TensorSections.monoidalUnitObjIso Y).inv =
      (TensorSections.monoidalUnitObjIso X).inv ≫ Functor.LaxMonoidal.ε F := by
  let F := Scheme.Modules.restrictFunctor f
  let : (Scheme.Modules.pullback f).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback f).symm
  let cY := TensorSections.monoidalUnitObjIso Y
  let cX := TensorSections.monoidalUnitObjIso X
  let r := Scheme.Modules.restrictUnitIso f
  have h := poleTensor_restrict_monoidalUnitObjIso f
  change F.map cY.hom ≫ r.hom =
    Functor.OplaxMonoidal.η F ≫ cX.hom at h
  let eL := F.mapIso cY ≪≫ r
  let eR := (Functor.Monoidal.εIso F).symm ≪≫ cX
  have he : eL = eR := Iso.ext h
  have hinv := congrArg Iso.inv he
  change r.inv ≫ F.map cY.inv =
    cX.inv ≫ Functor.LaxMonoidal.ε F at hinv
  exact hinv

theorem poleTensor_restrict_unitObjTensorIso_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    let F := Scheme.Modules.restrictFunctor f
    letI : (Scheme.Modules.pullback f).Monoidal :=
      PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
    letI : F.Monoidal := Functor.Monoidal.transport
      (Scheme.Modules.restrictFunctorIsoPullback f).symm
    (Scheme.Modules.restrictUnitIso f).inv ≫
        F.map (TensorSections.unitObjTensorIso Y).inv ≫
          (TensorSections.restrictMonoidalTensorIso f
            (Invertible.Scheme.Modules.unitObj Y) (Invertible.Scheme.Modules.unitObj Y)).hom =
      (TensorSections.unitObjTensorIso X).inv ≫
        ((Scheme.Modules.restrictUnitIso f).inv ⊗ₘ
          (Scheme.Modules.restrictUnitIso f).inv) := by
  let F := Scheme.Modules.restrictFunctor f
  let : (Scheme.Modules.pullback f).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback f).symm
  let cY := TensorSections.monoidalUnitObjIso Y
  let cX := TensorSections.monoidalUnitObjIso X
  let r := Scheme.Modules.restrictUnitIso f
  have hunit := poleTensor_restrict_monoidalUnitObjIso_inv f
  change r.inv ≫ F.map cY.inv =
    cX.inv ≫ Functor.LaxMonoidal.ε F at hunit
  have hunitForward := poleTensor_restrict_monoidalUnitObjIso f
  change F.map cY.hom ≫ r.hom =
    Functor.OplaxMonoidal.η F ≫ cX.hom at hunitForward
  have hunitHom :
      cX.hom ≫ r.inv =
        Functor.LaxMonoidal.ε F ≫ F.map cY.hom := by
    refine (r.comp_inv_eq).2 ?_
    have h₁ :
        (Functor.LaxMonoidal.ε F ≫ F.map cY.hom) ≫ r.hom =
          Functor.LaxMonoidal.ε F ≫ (F.map cY.hom ≫ r.hom) :=
      Category.assoc _ _ _
    have h₂ :
        Functor.LaxMonoidal.ε F ≫ (F.map cY.hom ≫ r.hom) =
          Functor.LaxMonoidal.ε F ≫
            (Functor.OplaxMonoidal.η F ≫ cX.hom) := congrArg
      (fun k : F.obj (𝟙_ Y.Modules) ⟶
          Invertible.Scheme.Modules.unitObj X ↦
        Functor.LaxMonoidal.ε F ≫ k)
      hunitForward
    have h₃ :
        Functor.LaxMonoidal.ε F ≫
            (Functor.OplaxMonoidal.η F ≫ cX.hom) =
          (Functor.LaxMonoidal.ε F ≫
            Functor.OplaxMonoidal.η F) ≫ cX.hom :=
      (Category.assoc _ _ _).symm
    have h₄ :
        (Functor.LaxMonoidal.ε F ≫
            Functor.OplaxMonoidal.η F) ≫ cX.hom = cX.hom :=
      (congrArg (fun k ↦ k ≫ cX.hom)
        (Functor.Monoidal.ε_η F)).trans (Category.id_comp cX.hom)
    exact (h₁.trans (h₂.trans (h₃.trans h₄))).symm
  have hepsilonTensor :
      Functor.LaxMonoidal.ε F ≫
          (λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) =
        (λ_ (𝟙_ X.Modules)).inv ≫
          (Functor.LaxMonoidal.ε F ⊗ₘ
            Functor.LaxMonoidal.ε F) := by
    calc
      _ = ((λ_ (𝟙_ X.Modules)).inv ≫
          (𝟙_ X.Modules ◁ Functor.LaxMonoidal.ε F)) ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) :=
        congrArg
          (fun k ↦ k ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)))
          (leftUnitor_inv_naturality (Functor.LaxMonoidal.ε F))
      _ = (λ_ (𝟙_ X.Modules)).inv ≫
          ((𝟙_ X.Modules ◁ Functor.LaxMonoidal.ε F) ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules))) :=
        Category.assoc _ _ _
      _ = _ := congrArg
        (fun k ↦ (λ_ (𝟙_ X.Modules)).inv ≫ k)
        (MonoidalCategory.tensorHom_def'
          (Functor.LaxMonoidal.ε F)
          (Functor.LaxMonoidal.ε F)).symm
  have htensorUnit :
      (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
          (F.map cY.hom ⊗ₘ F.map cY.hom) =
        (cX.hom ⊗ₘ cX.hom) ≫ (r.inv ⊗ₘ r.inv) := by
    have h₁ := tensorHom_comp_tensorHom
      (Functor.LaxMonoidal.ε F) (Functor.LaxMonoidal.ε F)
      (F.map cY.hom) (F.map cY.hom)
    have h₂ :
        (Functor.LaxMonoidal.ε F ≫ F.map cY.hom) ⊗ₘ
            (Functor.LaxMonoidal.ε F ≫ F.map cY.hom) =
          (cX.hom ≫ r.inv) ⊗ₘ (cX.hom ≫ r.inv) := congrArg
      (fun k : 𝟙_ X.Modules ⟶
          F.obj (Invertible.Scheme.Modules.unitObj Y) ↦ k ⊗ₘ k)
      hunitHom.symm
    have h₃ := tensorHom_comp_tensorHom
      cX.hom cX.hom r.inv r.inv
    exact h₁.trans (h₂.trans h₃.symm)
  have hcore := poleTensor_five_comp_of_three_eq
    hunit hepsilonTensor htensorUnit
  change r.inv ≫
      F.map (cY.inv ≫ (λ_ (𝟙_ Y.Modules)).inv ≫
        (cY.hom ⊗ₘ cY.hom)) ≫
        Functor.OplaxMonoidal.δ F
          (Invertible.Scheme.Modules.unitObj Y) (Invertible.Scheme.Modules.unitObj Y) =
    (cX.inv ≫ (λ_ (𝟙_ X.Modules)).inv ≫
      (cX.hom ⊗ₘ cX.hom)) ≫ (r.inv ⊗ₘ r.inv)
  have hmap :
      F.map (cY.inv ≫ (λ_ (𝟙_ Y.Modules)).inv ≫
          (cY.hom ⊗ₘ cY.hom)) =
        F.map cY.inv ≫ F.map (λ_ (𝟙_ Y.Modules)).inv ≫
          F.map (cY.hom ⊗ₘ cY.hom) := by
    calc
      _ = F.map cY.inv ≫
          F.map ((λ_ (𝟙_ Y.Modules)).inv ≫
            (cY.hom ⊗ₘ cY.hom)) :=
        F.map_comp cY.inv
          ((λ_ (𝟙_ Y.Modules)).inv ≫ (cY.hom ⊗ₘ cY.hom))
      _ = _ := congrArg (fun k ↦ F.map cY.inv ≫ k)
        (F.map_comp (λ_ (𝟙_ Y.Modules)).inv
          (cY.hom ⊗ₘ cY.hom))
  have hmapUnitor :
      F.map (λ_ (𝟙_ Y.Modules)).inv =
        (λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
          (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
            Functor.LaxMonoidal.μ F (𝟙_ Y.Modules) (𝟙_ Y.Modules) :=
    Functor.Monoidal.map_leftUnitor_inv F (𝟙_ Y.Modules)
  have hmapTensor :
      F.map (cY.hom ⊗ₘ cY.hom) =
        Functor.OplaxMonoidal.δ F (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
          (F.map cY.hom ⊗ₘ F.map cY.hom) ≫
            Functor.LaxMonoidal.μ F
              (Invertible.Scheme.Modules.unitObj Y) (Invertible.Scheme.Modules.unitObj Y) :=
    Functor.Monoidal.map_tensor F cY.hom cY.hom
  have hmapExpanded :
      F.map (cY.inv ≫ (λ_ (𝟙_ Y.Modules)).inv ≫
          (cY.hom ⊗ₘ cY.hom)) =
        F.map cY.inv ≫
          ((λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
              Functor.LaxMonoidal.μ F
                (𝟙_ Y.Modules) (𝟙_ Y.Modules)) ≫
          (Functor.OplaxMonoidal.δ F
              (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
            (F.map cY.hom ⊗ₘ F.map cY.hom) ≫
              Functor.LaxMonoidal.μ F
                (Invertible.Scheme.Modules.unitObj Y)
                (Invertible.Scheme.Modules.unitObj Y)) := by
    calc
      _ = F.map cY.inv ≫ F.map (λ_ (𝟙_ Y.Modules)).inv ≫
          F.map (cY.hom ⊗ₘ cY.hom) := hmap
      _ = F.map cY.inv ≫
          ((λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
              Functor.LaxMonoidal.μ F
                (𝟙_ Y.Modules) (𝟙_ Y.Modules)) ≫
          F.map (cY.hom ⊗ₘ cY.hom) := congrArg
        (fun k ↦ F.map cY.inv ≫ k ≫ F.map (cY.hom ⊗ₘ cY.hom))
        hmapUnitor
      _ = _ := congrArg
        (fun k ↦ F.map cY.inv ≫
          ((λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
              Functor.LaxMonoidal.μ F
                (𝟙_ Y.Modules) (𝟙_ Y.Modules)) ≫ k)
        hmapTensor
  calc
    _ = r.inv ≫
        (F.map cY.inv ≫
          ((λ_ (F.obj (𝟙_ Y.Modules))).inv ≫
            (Functor.LaxMonoidal.ε F ▷ F.obj (𝟙_ Y.Modules)) ≫
              Functor.LaxMonoidal.μ F
                (𝟙_ Y.Modules) (𝟙_ Y.Modules)) ≫
          (Functor.OplaxMonoidal.δ F
              (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
            (F.map cY.hom ⊗ₘ F.map cY.hom) ≫
              Functor.LaxMonoidal.μ F
                (Invertible.Scheme.Modules.unitObj Y)
                (Invertible.Scheme.Modules.unitObj Y))) ≫
          Functor.OplaxMonoidal.δ F
            (Invertible.Scheme.Modules.unitObj Y)
            (Invertible.Scheme.Modules.unitObj Y) := congrArg
      (fun k ↦ r.inv ≫ k ≫
        Functor.OplaxMonoidal.δ F
          (Invertible.Scheme.Modules.unitObj Y)
          (Invertible.Scheme.Modules.unitObj Y)) hmapExpanded
    _ = _ := by
      simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc,
        Functor.Monoidal.μ_δ, Category.comp_id]
      exact hcore

/-- Restricting a global pure tensor section to an affine open agrees, through the
restriction functor's monoidal comparison, with the pure tensor of the restricted sections. -/
theorem tensorSection_localTrivializationRestriction
    {X : Scheme.{u}} (M N : X.Modules) (U : X.affineOpens)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    (TensorSections.restrictMonoidalTensorIso U.1.ι M N).hom.val.app (.op ⊤)
        (FrameSections.localTrivializationRestriction (M ⊗ N) U
          (TensorSections.tensorSection M N ⊤ x y)) =
      TensorSections.tensorSection
        ((Scheme.Modules.restrictFunctor U.1.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.1.ι).obj N)
        ⊤
        (FrameSections.localTrivializationRestriction M U x)
        (FrameSections.localTrivializationRestriction N U y) := by
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : (Scheme.Modules.pullback U.1.ι).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal U.1.ι
  let : F.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).symm
  let r := Scheme.Modules.restrictUnitIso U.1.ι
  let uX := TensorSections.unitObjTensorIso X
  let uU := TensorSections.unitObjTensorIso U.1.toScheme
  let d := TensorSections.restrictMonoidalTensorIso U.1.ι M N
  let dUnit := TensorSections.restrictMonoidalTensorIso U.1.ι
    (Invertible.Scheme.Modules.unitObj X) (Invertible.Scheme.Modules.unitObj X)
  let hx := poleTopSectionHom M x
  let hy := poleTopSectionHom N y
  let q := TensorSections.tensorSection M N ⊤ x y
  let xU := FrameSections.localTrivializationRestriction M U x
  let yU := FrameSections.localTrivializationRestriction N U y
  let qU := FrameSections.localTrivializationRestriction (M ⊗ N) U q
  let tU := TensorSections.tensorSection (F.obj M) (F.obj N) ⊤ xU yU
  have hcomp := poleTopSectionHom_comp qU d.hom
  change poleTopSectionHom (F.obj (M ⊗ N)) qU ≫ d.hom =
    poleTopSectionHom (F.obj M ⊗ F.obj N)
      (d.hom.val.app (.op ⊤) qU) at hcomp
  have hrestrict :=
    poleTopSectionHom_localTrivializationRestriction (M ⊗ N) U q
  change poleTopSectionHom (F.obj (M ⊗ N)) qU =
    r.inv ≫ F.map (poleTopSectionHom (M ⊗ N) q) at hrestrict
  have hglobal := poleTopSectionHom_tensorTopSection M N x y
  change poleTopSectionHom (M ⊗ N) q =
    uX.inv ≫ (hx ⊗ₘ hy) at hglobal
  have hmapGlobal := congrArg F.map hglobal
  have hmapComp := F.map_comp uX.inv (hx ⊗ₘ hy)
  have hmapGlobalExpanded :
      F.map (poleTopSectionHom (M ⊗ N) q) =
        F.map uX.inv ≫ F.map (hx ⊗ₘ hy) :=
    hmapGlobal.trans hmapComp
  have hnatural := (Functor.OplaxMonoidal.δ_natural F hx hy).symm
  change F.map (hx ⊗ₘ hy) ≫ d.hom =
    dUnit.hom ≫ (F.map hx ⊗ₘ F.map hy) at hnatural
  have hunit := poleTensor_restrict_unitObjTensorIso_inv U.1.ι
  change r.inv ≫ F.map uX.inv ≫ dUnit.hom =
    uU.inv ≫ (r.inv ⊗ₘ r.inv) at hunit
  have htensor := tensorHom_comp_tensorHom
    r.inv r.inv (F.map hx) (F.map hy)
  have hrestrictX :=
    poleTopSectionHom_localTrivializationRestriction M U x
  change poleTopSectionHom (F.obj M) xU =
    r.inv ≫ F.map hx at hrestrictX
  have hrestrictY :=
    poleTopSectionHom_localTrivializationRestriction N U y
  change poleTopSectionHom (F.obj N) yU =
    r.inv ≫ F.map hy at hrestrictY
  have hlocal := poleTopSectionHom_tensorTopSection
    (F.obj M) (F.obj N) xU yU
  change poleTopSectionHom (F.obj M ⊗ F.obj N) tU =
    uU.inv ≫
      (poleTopSectionHom (F.obj M) xU ⊗ₘ
        poleTopSectionHom (F.obj N) yU) at hlocal
  have hmiddle := poleTensor_nested_four_comp_of_tail_head_last
    hnatural hunit htensor
  change (r.inv ≫
      (F.map uX.inv ≫ F.map (hx ⊗ₘ hy))) ≫ d.hom =
    uU.inv ≫
      ((r.inv ≫ F.map hx) ⊗ₘ (r.inv ≫ F.map hy)) at hmiddle
  have hhom :
      poleTopSectionHom (F.obj M ⊗ F.obj N) (d.hom.val.app (.op ⊤) qU) =
        poleTopSectionHom (F.obj M ⊗ F.obj N) tU := by
    have hchain :
        poleTopSectionHom (F.obj (M ⊗ N)) qU ≫ d.hom =
          poleTopSectionHom (F.obj M ⊗ F.obj N) tU := by
      have hstart :
          poleTopSectionHom (F.obj (M ⊗ N)) qU ≫ d.hom =
            (r.inv ≫ F.map (poleTopSectionHom (M ⊗ N) q)) ≫
              d.hom :=
        congrArg (fun k ↦ k ≫ d.hom) hrestrict
      have hglobalStep :
          (r.inv ≫ F.map (poleTopSectionHom (M ⊗ N) q)) ≫
              d.hom =
            (r.inv ≫ (F.map uX.inv ≫ F.map (hx ⊗ₘ hy))) ≫
              d.hom :=
        congrArg (fun k ↦ (r.inv ≫ k) ≫ d.hom) hmapGlobalExpanded
      have hrestricted :
          uU.inv ≫ ((r.inv ≫ F.map hx) ⊗ₘ
              (r.inv ≫ F.map hy)) =
            uU.inv ≫
              (poleTopSectionHom (F.obj M) xU ⊗ₘ
                poleTopSectionHom (F.obj N) yU) :=
        congrArg (fun k ↦ uU.inv ≫ k)
          (congrArg₂ (fun a b ↦ a ⊗ₘ b)
            hrestrictX.symm hrestrictY.symm)
      exact hstart.trans (hglobalStep.trans
        (hmiddle.trans (hrestricted.trans hlocal.symm)))
    exact hcomp.symm.trans hchain
  have happ := congrArg
    (fun k ↦ k.val.app (.op (⊤ : U.1.toScheme.Opens))
      (show U.1.toScheme.presheaf.obj (.op ⊤) from 1)) hhom
  exact (poleTopSectionHom_app_top_apply_one (F.obj M ⊗ F.obj N)
    (d.hom.val.app (.op ⊤) qU)).symm.trans
      (happ.trans (poleTopSectionHom_app_top_apply_one
        (F.obj M ⊗ F.obj N) tU))

/-- Under tensor-product trivializations on an affine open, the local coordinate of a
pure tensor section is the product of the two local coordinates. -/
theorem localTrivializationTopSection_tensorSection
    {X : Scheme.{u}} (M N : X.Modules) (U : X.affineOpens)
    (eM : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (eN : N.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (x : Γ(M, (⊤ : X.Opens))) (y : Γ(N, (⊤ : X.Opens))) :
    FrameSections.localTrivializationTopSection (M ⊗ N) U
        (TensorSections.restrictMonoidalTensorIso U.1.ι M N ≪≫
          (eM ⊗ᵢ eN) ≪≫ TensorSections.unitObjTensorIso U.1.toScheme)
        (TensorSections.tensorSection M N ⊤ x y) =
      FrameSections.localTrivializationTopSection M U eM x *
        FrameSections.localTrivializationTopSection N U eN y := by
  change
    (TensorSections.unitObjTensorIso U.1.toScheme).hom.val.app (.op ⊤)
      ((eM.hom ⊗ₘ eN.hom).val.app (.op ⊤)
        ((TensorSections.restrictMonoidalTensorIso U.1.ι M N).hom.val.app (.op ⊤)
          (FrameSections.localTrivializationRestriction (M ⊗ N) U
            (TensorSections.tensorSection M N ⊤ x y)))) = _
  rw [tensorSection_localTrivializationRestriction, tensorSection_map]
  exact unitObjTensorIso_hom_tensorSection_top U.1.toScheme
    (eM.hom.val.app (.op ⊤) (FrameSections.localTrivializationRestriction M U x))
    (eN.hom.val.app (.op ⊤) (FrameSections.localTrivializationRestriction N U y))

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections
