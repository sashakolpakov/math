/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackCompMonoidal
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackUnitMonoidal

/-! # Pullback Frame Composition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackFrameComposition

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u
local instance pullbackFrameMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance pullbackFrameFunctorMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f

/-- A monoidal comparison between two composite pullbacks preserves the
canonical trivialization of the monoidal unit. -/
theorem pullbackComp_monoidalUnitIso
    {X T U : Scheme.{u}} (f : T ⟶ X) (g : U ⟶ T) (h : U ⟶ X)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback h) [α.hom.IsMonoidal] :
    (Functor.Monoidal.εIso (Scheme.Modules.pullback h)).symm =
      (α.app (𝟙_ X.Modules)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  have hunit := NatTrans.IsMonoidal.unit (τ := α.hom)
  rw [Functor.LaxMonoidal.comp_ε] at hunit
  simp only [Category.assoc] at hunit
  change (Functor.Monoidal.εIso
      (Scheme.Modules.pullback g)).hom ≫
        (Scheme.Modules.pullback g).map
          (Functor.Monoidal.εIso
            (Scheme.Modules.pullback f)).hom ≫
        α.hom.app (𝟙_ X.Modules) =
      (Functor.Monoidal.εIso
        (Scheme.Modules.pullback h)).hom at hunit
  apply (cancel_epi
    (Functor.Monoidal.εIso (Scheme.Modules.pullback h)).hom).1
  rw [Iso.hom_inv_id]
  rw [← hunit]
  simp only [Category.assoc]
  slice_rhs 3 4 => erw [(α.app (𝟙_ X.Modules)).hom_inv_id]
  erw [Category.id_comp]
  slice_rhs 2 3 => erw [Functor.Monoidal.map_ε_η]
  simp

/-- A monoidal comparison between two composite pullbacks preserves the
canonical tensor frame induced by two monoidal-unit-valued frames. -/
theorem pullbackComp_monoidalTensorTrivialization
    {X T U : Scheme.{u}} (f : T ⟶ X) (g : U ⟶ T) (h : U ⟶ X)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback h) [α.hom.IsMonoidal]
    (M N : X.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ 𝟙_ T.Modules)
    (d : (Scheme.Modules.pullback f).obj N ≅ 𝟙_ T.Modules) :
    (Functor.Monoidal.μIso (Scheme.Modules.pullback h) M N).symm ≪≫
        (((α.app M).symm ≪≫ (Scheme.Modules.pullback g).mapIso e ≪≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm) ⊗ᵢ
          ((α.app N).symm ≪≫ (Scheme.Modules.pullback g).mapIso d ≪≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm)) ≪≫
        λ_ (𝟙_ U.Modules) =
      (α.app (M ⊗ N)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          ((Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
            (e ⊗ᵢ d) ≪≫ λ_ (𝟙_ T.Modules)) ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    MonoidalCategory.tensorIso_hom]
  have htensor := NatTrans.IsMonoidal.tensor (τ := α.hom) M N
  change (Functor.Monoidal.μIso
      (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g) M N).hom ≫
        (α.app (M ⊗ N)).hom =
    ((α.app M).hom ⊗ₘ (α.app N).hom) ≫
      (Functor.Monoidal.μIso (Scheme.Modules.pullback h) M N).hom at htensor
  have hhom_delta :
      (α.app (M ⊗ N)).hom ≫
          Functor.OplaxMonoidal.δ (Scheme.Modules.pullback h) M N =
        Functor.OplaxMonoidal.δ
            (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g) M N ≫
          ((α.app M).hom ⊗ₘ (α.app N).hom) := by
    apply (cancel_epi (Functor.Monoidal.μIso
      (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g) M N).hom).1
    slice_lhs 1 2 => rw [htensor]
    slice_lhs 2 3 => erw [Functor.Monoidal.μ_δ]
    slice_rhs 1 2 => erw [Functor.Monoidal.μ_δ]
    simp
  have hinv_delta :
      (α.app (M ⊗ N)).inv ≫
          Functor.OplaxMonoidal.δ
            (Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g) M N =
        Functor.OplaxMonoidal.δ (Scheme.Modules.pullback h) M N ≫
          ((α.app M).inv ⊗ₘ (α.app N).inv) := by
    apply (cancel_epi (α.app (M ⊗ N)).hom).1
    slice_lhs 1 2 => erw [(α.app (M ⊗ N)).hom_inv_id]
    rw [Category.id_comp]
    slice_rhs 1 2 => rw [hhom_delta]
    slice_rhs 2 3 => erw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  let p := e.hom
  let q := d.hom
  let etaG := Functor.OplaxMonoidal.η (Scheme.Modules.pullback g)
  have hunit_tensor :
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g)
          (𝟙_ T.Modules) (𝟙_ T.Modules) ≫
          (etaG ⊗ₘ etaG) ≫ (λ_ (𝟙_ U.Modules)).hom =
        (Scheme.Modules.pullback g).map (λ_ (𝟙_ T.Modules)).hom ≫ etaG := by
    dsimp only [etaG]
    rw [tensorHom_def]
    simp only [Category.assoc]
    rw [MonoidalCategory.leftUnitor_naturality]
    rw [Functor.OplaxMonoidal.left_unitality_hom_assoc]
  have hchain :
      (((α.app M).inv ≫ (Scheme.Modules.pullback g).map p ≫ etaG) ⊗ₘ
          ((α.app N).inv ≫ (Scheme.Modules.pullback g).map q ≫ etaG)) =
        ((α.app M).inv ⊗ₘ (α.app N).inv) ≫
          ((Scheme.Modules.pullback g).map p ⊗ₘ
            (Scheme.Modules.pullback g).map q) ≫ (etaG ⊗ₘ etaG) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  change
    Functor.OplaxMonoidal.δ (Scheme.Modules.pullback h) M N ≫
          (((α.app M).inv ≫
              (Scheme.Modules.pullback g).map p ≫ etaG) ⊗ₘ
            ((α.app N).inv ≫
              (Scheme.Modules.pullback g).map q ≫ etaG)) ≫
          (λ_ (𝟙_ U.Modules)).hom =
      (α.app (M ⊗ N)).inv ≫
        (Scheme.Modules.pullback g).map
          (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) M N ≫
            (p ⊗ₘ q) ≫ (λ_ (𝟙_ T.Modules)).hom) ≫ etaG
  rw [hchain]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [← hinv_delta]
  rw [Functor.OplaxMonoidal.comp_δ]
  slice_lhs 3 4 => erw [Functor.OplaxMonoidal.δ_natural]
  slice_lhs 4 6 => rw [hunit_tensor]
  simp only [Functor.map_comp]
  erw [Category.assoc]
  erw [Category.assoc]

/-- Converting two structure-sheaf-valued pullback frames to monoidal-unit
frames commutes with forming their canonical tensor frame. -/
theorem pullbackTensorTrivialization_eq_monoidal
    {X T : Scheme.{u}} (f : T ⟶ X) (M N : X.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ Invertible.Scheme.Modules.unitObj T)
    (d : (Scheme.Modules.pullback f).obj N ≅ Invertible.Scheme.Modules.unitObj T) :
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
        (e ⊗ᵢ d) ≪≫ TensorSections.unitObjTensorIso T =
      (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
        ((e ≪≫ (TensorSections.monoidalUnitObjIso T).symm) ⊗ᵢ
          (d ≪≫ (TensorSections.monoidalUnitObjIso T).symm)) ≪≫
        λ_ (𝟙_ T.Modules) ≪≫ TensorSections.monoidalUnitObjIso T := by
  apply Iso.ext
  simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom,
    TensorSections.unitObjTensorIso, Iso.symm_hom]
  slice_lhs 2 3 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.assoc]

/-- A monoidal comparison between two composite pullbacks preserves the
canonical tensor frame induced by two structure-sheaf-valued frames. -/
theorem pullbackComp_tensorTrivialization
    {X T U : Scheme.{u}} (f : T ⟶ X) (g : U ⟶ T) (h : U ⟶ X)
    (α : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback h) [α.hom.IsMonoidal]
    (M N : X.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅ Invertible.Scheme.Modules.unitObj T)
    (d : (Scheme.Modules.pullback f).obj N ≅ Invertible.Scheme.Modules.unitObj T) :
    (Functor.Monoidal.μIso (Scheme.Modules.pullback h) M N).symm ≪≫
        (((α.app M).symm ≪≫ (Scheme.Modules.pullback g).mapIso e ≪≫
            Invertible.Scheme.Modules.pullbackUnitIso g) ⊗ᵢ
          ((α.app N).symm ≪≫ (Scheme.Modules.pullback g).mapIso d ≪≫
            Invertible.Scheme.Modules.pullbackUnitIso g)) ≪≫
        TensorSections.unitObjTensorIso U =
      (α.app (M ⊗ N)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          ((Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
            (e ⊗ᵢ d) ≪≫ TensorSections.unitObjTensorIso T) ≪≫
        Invertible.Scheme.Modules.pullbackUnitIso g := by
  let uT := TensorSections.monoidalUnitObjIso T
  let uU := TensorSections.monoidalUnitObjIso U
  let e₀ := e ≪≫ uT.symm
  let d₀ := d ≪≫ uT.symm
  let eComp := (α.app M).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫
      Invertible.Scheme.Modules.pullbackUnitIso g
  let dComp := (α.app N).symm ≪≫
    (Scheme.Modules.pullback g).mapIso d ≪≫
      Invertible.Scheme.Modules.pullbackUnitIso g
  let eComp₀ := (α.app M).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e₀ ≪≫
      (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm
  let dComp₀ := (α.app N).symm ≪≫
    (Scheme.Modules.pullback g).mapIso d₀ ≪≫
      (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm
  have hunit := PullbackUnitMonoidal.Scheme.Modules.pullback_monoidalUnitObjIso g
  change (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm ≪≫ uU =
    (Scheme.Modules.pullback g).mapIso uT ≪≫
      Invertible.Scheme.Modules.pullbackUnitIso g at hunit
  have hunitHom := congrArg Iso.hom hunit
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at hunitHom
  change (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv ≫ uU.hom =
    ((Scheme.Modules.pullback g).mapIso uT).hom ≫
      (Invertible.Scheme.Modules.pullbackUnitIso g).hom at hunitHom
  have hunitInv :
      Invertible.Scheme.Modules.pullbackUnitIso g ≪≫ uU.symm =
        ((Scheme.Modules.pullback g).mapIso uT).symm ≪≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).symm := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom]
    calc
      (Invertible.Scheme.Modules.pullbackUnitIso g).hom ≫ uU.inv =
          ((Scheme.Modules.pullback g).mapIso uT).inv ≫
            (((Scheme.Modules.pullback g).mapIso uT).hom ≫
              (Invertible.Scheme.Modules.pullbackUnitIso g).hom) ≫ uU.inv := by simp
      _ = ((Scheme.Modules.pullback g).mapIso uT).inv ≫
          (((Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv ≫
            uU.hom) ≫ uU.inv) := by rw [hunitHom]
      _ = ((Scheme.Modules.pullback g).mapIso uT).inv ≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv := by simp
  have hsimpleE : eComp ≪≫ uU.symm = eComp₀ := by
    apply Iso.ext
    simp only [eComp, eComp₀, e₀, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Category.assoc]
    rw [← Category.assoc]
    rw [show (Invertible.Scheme.Modules.pullbackUnitIso g).hom ≫ uU.inv =
        ((Scheme.Modules.pullback g).mapIso uT).inv ≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv by
      exact congrArg Iso.hom hunitInv]
    have hmapComp :=
      ((Scheme.Modules.pullback g).map_comp e.hom uT.inv).symm
    calc
      (α.app M).inv ≫ (Scheme.Modules.pullback g).map e.hom ≫
            (Scheme.Modules.pullback g).map uT.inv ≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv =
          (α.app M).inv ≫
            ((Scheme.Modules.pullback g).map e.hom ≫
              (Scheme.Modules.pullback g).map uT.inv) ≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv := by
        simp only [Category.assoc]
      _ = (α.app M).inv ≫
            ((Scheme.Modules.pullback g).map (e.hom ≫ uT.inv) ≫
              (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv) :=
        congrArg (fun q ↦ (α.app M).inv ≫
          (q ≫ (Functor.Monoidal.εIso
            (Scheme.Modules.pullback g)).inv)) hmapComp
      _ = _ := rfl
  have hsimpleD : dComp ≪≫ uU.symm = dComp₀ := by
    apply Iso.ext
    simp only [dComp, dComp₀, d₀, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Category.assoc]
    rw [← Category.assoc]
    rw [show (Invertible.Scheme.Modules.pullbackUnitIso g).hom ≫ uU.inv =
        ((Scheme.Modules.pullback g).mapIso uT).inv ≫
          (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv by
      exact congrArg Iso.hom hunitInv]
    have hmapComp :=
      ((Scheme.Modules.pullback g).map_comp d.hom uT.inv).symm
    calc
      (α.app N).inv ≫ (Scheme.Modules.pullback g).map d.hom ≫
            (Scheme.Modules.pullback g).map uT.inv ≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv =
          (α.app N).inv ≫
            ((Scheme.Modules.pullback g).map d.hom ≫
              (Scheme.Modules.pullback g).map uT.inv) ≫
            (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv := by
        simp only [Category.assoc]
      _ = (α.app N).inv ≫
            ((Scheme.Modules.pullback g).map (d.hom ≫ uT.inv) ≫
              (Functor.Monoidal.εIso (Scheme.Modules.pullback g)).inv) :=
        congrArg (fun q ↦ (α.app N).inv ≫
          (q ≫ (Functor.Monoidal.εIso
            (Scheme.Modules.pullback g)).inv)) hmapComp
      _ = _ := rfl
  change
    (Functor.Monoidal.μIso (Scheme.Modules.pullback h) M N).symm ≪≫
        (eComp ⊗ᵢ dComp) ≪≫ TensorSections.unitObjTensorIso U =
      (α.app (M ⊗ N)).symm ≪≫
        (Scheme.Modules.pullback g).mapIso
          ((Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
            (e ⊗ᵢ d) ≪≫ TensorSections.unitObjTensorIso T) ≪≫
        Invertible.Scheme.Modules.pullbackUnitIso g
  rw [pullbackTensorTrivialization_eq_monoidal h M N eComp dComp]
  rw [hsimpleE, hsimpleD]
  dsimp only [eComp₀, dComp₀]
  have hmonoidalU := congrArg (fun q ↦ q ≪≫ uU)
    (pullbackComp_monoidalTensorTrivialization f g h α M N e₀ d₀)
  simp only [CategoryTheory.Iso.trans_assoc] at hmonoidalU
  rw [hmonoidalU]
  rw [hunit]
  have hmap :
      (Scheme.Modules.pullback g).mapIso
          ((Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
            (e₀ ⊗ᵢ d₀) ≪≫ λ_ (𝟙_ T.Modules)) ≪≫
        (Scheme.Modules.pullback g).mapIso uT =
      (Scheme.Modules.pullback g).mapIso
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
          (e ⊗ᵢ d) ≪≫ TensorSections.unitObjTensorIso T) := by
    rw [← (Scheme.Modules.pullback g).mapIso_trans]
    simpa only [e₀, d₀, uT, CategoryTheory.Iso.trans_assoc] using congrArg
      (Scheme.Modules.pullback g).mapIso
      (pullbackTensorTrivialization_eq_monoidal f M N e d).symm
  have hmap' := congrArg
    (fun q ↦ q ≪≫ Invertible.Scheme.Modules.pullbackUnitIso g) hmap
  rw [CategoryTheory.Iso.trans_assoc] at hmap'
  have hmap'' := congrArg
    (fun q ↦ (α.app (M ⊗ N)).symm ≪≫ q) hmap'
  exact hmap''

/-- The canonical restriction-functor tensor frame is its direct pullback
presentation after inserting the restriction-pullback comparison. -/
theorem restrictMonoidalTensorTrivialization_eq_pullback
    {X T : Scheme.{u}} (f : T ⟶ X) [IsOpenImmersion f]
    (M N : X.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅
      Invertible.Scheme.Modules.unitObj T)
    (d : (Scheme.Modules.restrictFunctor f).obj N ≅
      Invertible.Scheme.Modules.unitObj T) :
    TensorSections.restrictMonoidalTensorIso f M N ≪≫ (e ⊗ᵢ d) ≪≫
        TensorSections.unitObjTensorIso T =
      (Scheme.Modules.restrictFunctorIsoPullback f).app (M ⊗ N) ≪≫
        (Functor.Monoidal.μIso (Scheme.Modules.pullback f) M N).symm ≪≫
        (((Scheme.Modules.restrictFunctorIsoPullback f).symm.app M ≪≫ e) ⊗ᵢ
          ((Scheme.Modules.restrictFunctorIsoPullback f).symm.app N ≪≫ d)) ≪≫
        TensorSections.unitObjTensorIso T := by
  apply Iso.ext
  simp only [TensorSections.restrictMonoidalTensorIso, Iso.trans_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [MonoidalCategory.tensorHom_comp_tensorHom]

/-- The inverse comparison between pullbacks along equal morphisms is
monoidal. -/
theorem pullbackCongr_inv_isMonoidal
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) :
    (Scheme.Modules.pullbackCongr hfg).inv.IsMonoidal := by
  subst g
  change NatTrans.IsMonoidal (𝟙 (Scheme.Modules.pullback f))
  infer_instance

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackFrameComposition
