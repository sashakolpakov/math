/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorGeneral

/-! # Presheaf Pullback Comp Monoidal -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PresheafPullbackCompMonoidal.PresheafOfModules

open _root_.PresheafOfModules

/-!
# Monoidality of presheaf pullback composition

The canonical comparison from iterated pullback to pullback along a composite morphism
of schemes is monoidal for the presheaf-of-modules tensor products.
-/

universe u

open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory

/-- The canonical presheaf pullback-composition comparison is monoidal. -/
theorem pullbackComp_hom_isMonoidal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI : MonoidalCategory (PresheafOfModules
      ((TopologicalSpace.Opens.map f.base).op ⋙
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) := by
      rw [show (TopologicalSpace.Opens.map f.base).op ⋙
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) =
          ((TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) ⋙
            forget₂ CommRingCat RingCat by rfl]
      exact PresheafOfModulesOfCommRing.monoidalCategory
    letI := PullbackTensorGeneral.PresheafOfModules.pullbackMonoidal g
    letI := PullbackTensorGeneral.PresheafOfModules.pullbackMonoidal f
    letI : (pullback
        (F := TopologicalSpace.Opens.map g.base ⋙ TopologicalSpace.Opens.map f.base)
        (R := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
        (PullbackTensorGeneral.PresheafOfModules.schemeRingPresheafHom g ≫ Functor.whiskerLeft
          (TopologicalSpace.Opens.map g.base).op (PullbackTensorGeneral.PresheafOfModules.schemeRingPresheafHom f))).Monoidal := by
      change (pullback (PullbackTensorGeneral.PresheafOfModules.schemeRingPresheafHom (f ≫ g))).Monoidal
      exact PullbackTensorGeneral.PresheafOfModules.pullbackMonoidal (f ≫ g)
    (pullbackComp (PullbackTensorGeneral.PresheafOfModules.schemeRingPresheafHom g) (PullbackTensorGeneral.PresheafOfModules.schemeRingPresheafHom f)).hom.IsMonoidal := by
  let : MonoidalCategory (PresheafOfModules
    ((TopologicalSpace.Opens.map f.base).op ⋙
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) := by
    rw [show (TopologicalSpace.Opens.map f.base).op ⋙
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) =
        ((TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) ⋙
          forget₂ CommRingCat RingCat by rfl]
    exact PresheafOfModulesOfCommRing.monoidalCategory
  let φg := PullbackTensorGeneral.PresheafOfModules.schemeRingPresheafHom g
  let φf := PullbackTensorGeneral.PresheafOfModules.schemeRingPresheafHom f
  let φfg := PullbackTensorGeneral.PresheafOfModules.schemeRingPresheafHom (f ≫ g)
  let qG : (PullbackTensorGeneral.PresheafOfModules.pushforwardFactored φg).LaxMonoidal :=
    PullbackTensorGeneral.PresheafOfModules.pushforwardFactoredLaxMonoidal φg
  let qF : (PullbackTensorGeneral.PresheafOfModules.pushforwardFactored φf).LaxMonoidal :=
    PullbackTensorGeneral.PresheafOfModules.pushforwardFactoredLaxMonoidal φf
  let qFG : (PullbackTensorGeneral.PresheafOfModules.pushforwardFactored φfg).LaxMonoidal :=
    PullbackTensorGeneral.PresheafOfModules.pushforwardFactoredLaxMonoidal φfg
  let oG : (pullback φg).OplaxMonoidal := PullbackTensorGeneral.PresheafOfModules.pullbackOplaxMonoidal φg
  have : IsIso (Functor.OplaxMonoidal.η (pullback φg)) := PullbackTensorGeneral.PresheafOfModules.isIso_pullback_η g
  have : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φg) P Q) :=
    fun P Q => PullbackTensorGeneral.PresheafOfModules.isIso_pullback_δ g P Q
  let hG : (pullback φg).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φg)
  let oF : (pullback φf).OplaxMonoidal := PullbackTensorGeneral.PresheafOfModules.pullbackOplaxMonoidal φf
  have : IsIso (Functor.OplaxMonoidal.η (pullback φf)) := PullbackTensorGeneral.PresheafOfModules.isIso_pullback_η f
  have : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φf) P Q) :=
    fun P Q => PullbackTensorGeneral.PresheafOfModules.isIso_pullback_δ f P Q
  let hF : (pullback φf).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φf)
  let oFG : (pullback φfg).OplaxMonoidal := PullbackTensorGeneral.PresheafOfModules.pullbackOplaxMonoidal φfg
  have : IsIso (Functor.OplaxMonoidal.η (pullback φfg)) := PullbackTensorGeneral.PresheafOfModules.isIso_pullback_η (f ≫ g)
  have : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (pullback φfg) P Q) :=
    fun P Q => PullbackTensorGeneral.PresheafOfModules.isIso_pullback_δ (f ≫ g) P Q
  let hFG : (pullback φfg).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback φfg)
  let hComp : (pullback
      (F := TopologicalSpace.Opens.map g.base ⋙ TopologicalSpace.Opens.map f.base)
      (R := X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)
      (φg ≫ Functor.whiskerLeft (TopologicalSpace.Opens.map g.base).op φf)).Monoidal := by
    change (pullback φfg).Monoidal
    exact hFG
  let hadjG : (PullbackTensorGeneral.PresheafOfModules.pullbackPushforwardFactoredAdjunction φg).IsMonoidal := by
    infer_instance
  let hadjF : (PullbackTensorGeneral.PresheafOfModules.pullbackPushforwardFactoredAdjunction φf).IsMonoidal := by
    infer_instance
  let hadjFG : (PullbackTensorGeneral.PresheafOfModules.pullbackPushforwardFactoredAdjunction φfg).IsMonoidal := by
    infer_instance
  let pG : (pushforward φg).LaxMonoidal := by
    change (PullbackTensorGeneral.PresheafOfModules.pushforwardFactored φg).LaxMonoidal
    exact qG
  let pF : (pushforward φf).LaxMonoidal := by
    change (PullbackTensorGeneral.PresheafOfModules.pushforwardFactored φf).LaxMonoidal
    exact qF
  let pFG : (pushforward φfg).LaxMonoidal := by
    change (PullbackTensorGeneral.PresheafOfModules.pushforwardFactored φfg).LaxMonoidal
    exact qFG
  have hadjOrigG : (pullbackPushforwardAdjunction φg).IsMonoidal := by
    rw [← PullbackTensorGeneral.PresheafOfModules.pullbackPushforwardFactoredAdjunction_eq φg]
    exact hadjG
  have hadjOrigF : (pullbackPushforwardAdjunction φf).IsMonoidal := by
    rw [← PullbackTensorGeneral.PresheafOfModules.pullbackPushforwardFactoredAdjunction_eq φf]
    exact hadjF
  have hadjOrigFG : (pullbackPushforwardAdjunction φfg).IsMonoidal := by
    rw [← PullbackTensorGeneral.PresheafOfModules.pullbackPushforwardFactoredAdjunction_eq φfg]
    exact hadjFG
  let α : pushforward φfg ⟶ pushforward φf ⋙ pushforward φg :=
    (pushforwardComp φg φf).inv
  have hα : α.IsMonoidal := by
    refine { unit := ?_, tensor := fun M N => ?_ }
    · rfl
    · ext1 U
      refine ModuleCat.MonoidalCategory.tensor_ext (fun x y => ?_)
      rfl
  have hadjOrigComp : ((pullbackPushforwardAdjunction φg).comp
      (pullbackPushforwardAdjunction φf)).IsMonoidal := by
    let := hadjOrigG
    let := hadjOrigF
    infer_instance
  have hmate : ((conjugateEquiv
      (pullbackPushforwardAdjunction φfg)
      ((pullbackPushforwardAdjunction φg).comp
        (pullbackPushforwardAdjunction φf))).symm α).IsMonoidal :=
    PullbackTensorGeneral.CategoryTheory.conjugateEquiv_symm_isMonoidal _ _ hadjOrigFG hadjOrigComp α hα
  rw [pullbackComp, Adjunction.leftAdjointCompIso_hom]
  exact hmate

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PresheafPullbackCompMonoidal.PresheafOfModules
