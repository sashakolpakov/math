/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenPullbackFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackFrameComposition

/-! # Tensor Frame Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameRestriction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u
local instance tensorRestrictionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance tensorRestrictionPullbackMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal := PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f

/-- The canonical structure-sheaf trivialization restricts compatibly along
nested opens. -/
theorem restrictMonoidalUnitTrivialization_restrictOpen
    {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU
        (TensorSections.restrictMonoidalUnitIso U.ι ≪≫ TensorSections.monoidalUnitObjIso U.toScheme) =
      TensorSections.restrictMonoidalUnitIso V.ι ≪≫ TensorSections.monoidalUnitObjIso V.toScheme := by
  rw [OpenPullbackFrame.Scheme.Modules.restrictOpenTrivialization_eq_pullback]
  apply Iso.ext
  let j := X.homOfLE hVU
  let α : Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback j ≅
      Scheme.Modules.pullback V.ι :=
    Scheme.Modules.pullbackComp j U.ι ≪≫
      (Scheme.Modules.pullbackCongr (X.homOfLE_ι hVU).symm).symm
  let hcomp : (Scheme.Modules.pullbackComp j U.ι).hom.IsMonoidal :=
    PullbackCompMonoidal.Scheme.Modules.pullbackComp_hom_isMonoidal j U.ι
  let hcongr :
      (Scheme.Modules.pullbackCongr
        (X.homOfLE_ι hVU).symm).inv.IsMonoidal :=
    PullbackFrameComposition.pullbackCongr_inv_isMonoidal (X.homOfLE_ι hVU).symm
  let halpha : α.hom.IsMonoidal := by
    change NatTrans.IsMonoidal
      ((Scheme.Modules.pullbackComp j U.ι).hom ≫
        (Scheme.Modules.pullbackCongr
          (X.homOfLE_ι hVU).symm).inv)
    exact NatTrans.IsMonoidal.comp _ _
  let rU := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app
    (𝟙_ X.Modules)
  let rV := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app
    (𝟙_ X.Modules)
  let eU := (Functor.Monoidal.εIso
    (Scheme.Modules.pullback U.ι)).symm
  let eV := (Functor.Monoidal.εIso
    (Scheme.Modules.pullback V.ι)).symm
  let eJ := (Functor.Monoidal.εIso
    (Scheme.Modules.pullback j)).symm
  let sU := TensorSections.monoidalUnitObjIso U.toScheme
  let sV := TensorSections.monoidalUnitObjIso V.toScheme
  let pU := Invertible.Scheme.Modules.pullbackUnitIso j
  have hcancel : rU.inv ≫ (rU ≪≫ eU ≪≫ sU).hom =
      (eU ≪≫ sU).hom := by simp
  have hunitComp := congrArg Iso.hom
    (PullbackFrameComposition.pullbackComp_monoidalUnitIso U.ι j V.ι α)
  have hunitObj := congrArg Iso.hom
    (PullbackUnitMonoidal.Scheme.Modules.pullback_monoidalUnitObjIso j)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    at hunitComp hunitObj
  change eV.hom = α.inv.app (𝟙_ X.Modules) ≫
    (Scheme.Modules.pullback j).map eU.hom ≫ eJ.hom at hunitComp
  change eJ.hom ≫ sV.hom =
    (Scheme.Modules.pullback j).map sU.hom ≫ pU.hom at hunitObj
  simp only [OpenPullbackFrame.Scheme.Modules.restrictOpenTrivializationPullback,
    Invertible.Scheme.Modules.restrictTrivialization, TensorSections.restrictMonoidalUnitIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change rV.hom ≫ α.inv.app (𝟙_ X.Modules) ≫
      (Scheme.Modules.pullback j).map
        (rU.inv ≫ (rU ≪≫ eU ≪≫ sU).hom) ≫ pU.hom =
      rV.hom ≫ eV.hom ≫ sV.hom
  calc
    _ = rV.hom ≫ α.inv.app (𝟙_ X.Modules) ≫
        (Scheme.Modules.pullback j).map (eU ≪≫ sU).hom ≫
        pU.hom := by
      rw [hcancel]
    _ = rV.hom ≫ α.inv.app (𝟙_ X.Modules) ≫
        (Scheme.Modules.pullback j).map eU.hom ≫
        (Scheme.Modules.pullback j).map sU.hom ≫ pU.hom := by
      simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
    _ = rV.hom ≫ α.inv.app (𝟙_ X.Modules) ≫
        (Scheme.Modules.pullback j).map eU.hom ≫ eJ.hom ≫ sV.hom := by
      rw [← hunitObj]
    _ = rV.hom ≫ eV.hom ≫ sV.hom := by
      simpa only [Category.assoc] using
        congrArg (fun q ↦ rV.hom ≫ q ≫ sV.hom) hunitComp.symm

/-- Restricting a canonical tensor frame to a smaller open agrees with the
tensor frame induced by restricting its two factors. -/
theorem restrictMonoidalTensorTrivialization_restrictOpen
    {X : Scheme.{u}} (M N : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (d : N.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU
        (TensorSections.restrictMonoidalTensorIso U.ι M N ≪≫ (e ⊗ᵢ d) ≪≫
          TensorSections.unitObjTensorIso U.toScheme) =
      TensorSections.restrictMonoidalTensorIso V.ι M N ≪≫
        (OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU e ⊗ᵢ
          OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU d) ≪≫
        TensorSections.unitObjTensorIso V.toScheme := by
  let j := X.homOfLE hVU
  let α : Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback j ≅
      Scheme.Modules.pullback V.ι :=
    Scheme.Modules.pullbackComp j U.ι ≪≫
      (Scheme.Modules.pullbackCongr (X.homOfLE_ι hVU).symm).symm
  let hcomp : (Scheme.Modules.pullbackComp j U.ι).hom.IsMonoidal :=
    PullbackCompMonoidal.Scheme.Modules.pullbackComp_hom_isMonoidal j U.ι
  let hcongr :
      (Scheme.Modules.pullbackCongr
        (X.homOfLE_ι hVU).symm).inv.IsMonoidal :=
    PullbackFrameComposition.pullbackCongr_inv_isMonoidal (X.homOfLE_ι hVU).symm
  let halpha : α.hom.IsMonoidal := by
    change NatTrans.IsMonoidal
      ((Scheme.Modules.pullbackComp j U.ι).hom ≫
        (Scheme.Modules.pullbackCongr
          (X.homOfLE_ι hVU).symm).inv)
    exact NatTrans.IsMonoidal.comp _ _
  let eU := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e
  let dU := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app N ≪≫ d
  let eV := (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app M ≪≫
    OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU e
  let dV := (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app N ≪≫
    OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU d
  let eComp := (α.app M).symm ≪≫
    (Scheme.Modules.pullback j).mapIso eU ≪≫
      Invertible.Scheme.Modules.pullbackUnitIso j
  let dComp := (α.app N).symm ≪≫
    (Scheme.Modules.pullback j).mapIso dU ≪≫
      Invertible.Scheme.Modules.pullbackUnitIso j
  have heV : eV = eComp := by
    dsimp only [eV]
    rw [OpenPullbackFrame.Scheme.Modules.restrictOpenTrivialization_eq_pullback hVU e]
    apply Iso.ext
    simp only [eComp, OpenPullbackFrame.Scheme.Modules.restrictOpenTrivializationPullback,
      Invertible.Scheme.Modules.restrictTrivialization, eU, α, j,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp
  have hdV : dV = dComp := by
    dsimp only [dV]
    rw [OpenPullbackFrame.Scheme.Modules.restrictOpenTrivialization_eq_pullback hVU d]
    apply Iso.ext
    simp only [dComp, OpenPullbackFrame.Scheme.Modules.restrictOpenTrivializationPullback,
      Invertible.Scheme.Modules.restrictTrivialization, dU, α, j,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp
  rw [PullbackFrameComposition.restrictMonoidalTensorTrivialization_eq_pullback V.ι M N
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU e)
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU d)]
  change _ = (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (M ⊗ N) ≪≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback V.ι) M N).symm ≪≫
      (eV ⊗ᵢ dV) ≪≫ TensorSections.unitObjTensorIso V.toScheme
  rw [heV, hdV]
  rw [PullbackFrameComposition.pullbackComp_tensorTrivialization U.ι j V.ι α M N eU dU]
  rw [OpenPullbackFrame.Scheme.Modules.restrictOpenTrivialization_eq_pullback hVU
    (TensorSections.restrictMonoidalTensorIso U.ι M N ≪≫ (e ⊗ᵢ d) ≪≫
      TensorSections.unitObjTensorIso U.toScheme)]
  simp only [OpenPullbackFrame.Scheme.Modules.restrictOpenTrivializationPullback,
    Invertible.Scheme.Modules.restrictTrivialization]
  rw [PullbackFrameComposition.restrictMonoidalTensorTrivialization_eq_pullback U.ι M N e d]
  simp only [eU, dU, α, j]
  let rInv := (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app (M ⊗ N)
  let rHom := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app (M ⊗ N)
  let q := (Functor.Monoidal.μIso (Scheme.Modules.pullback U.ι) M N).symm ≪≫
    (((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e) ⊗ᵢ
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app N ≪≫ d)) ≪≫
    TensorSections.unitObjTensorIso U.toScheme
  have hinside : rInv ≪≫ rHom ≪≫ q = q := by
    dsimp only [rInv, rHom]
    apply Iso.ext
    simp
  have hmapInside := congrArg
    (fun k ↦ (Scheme.Modules.pullback j).mapIso k) hinside
  dsimp only [rInv, rHom, q] at hmapInside
  have halphaApp :
      (α.app (M ⊗ N)).symm =
        (Scheme.Modules.pullbackCongr
            (X.homOfLE_ι hVU).symm).app (M ⊗ N) ≪≫
          ((Scheme.Modules.pullbackComp j U.ι).app (M ⊗ N)).symm := by
    rfl
  rw [halphaApp]
  have hfull := congrArg
    (fun k ↦ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (M ⊗ N) ≪≫
      (Scheme.Modules.pullbackCongr
          (X.homOfLE_ι hVU).symm).app (M ⊗ N) ≪≫
      ((Scheme.Modules.pullbackComp j U.ι).app (M ⊗ N)).symm ≪≫ k ≪≫
      Invertible.Scheme.Modules.pullbackUnitIso j) hmapInside
  simpa only [j, CategoryTheory.Iso.trans_assoc] using hfull

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameRestriction
