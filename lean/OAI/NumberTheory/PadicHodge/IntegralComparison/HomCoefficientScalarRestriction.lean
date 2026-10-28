import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveScalarHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomPresheafDualFrame
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Whiskering

/-! # Hom Coefficient Scalar Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientScalarRestriction

noncomputable section

/-! Restriction along a surjective scalar map identifies the actual
coefficient Hom presheaves and preserves evaluation at every vector. -/
open _root_.CategoryTheory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type v} [Category C]
  (A Q : Type u) [CommRing A] [CommRing Q] [Algebra A Q]
  (hQ : Function.Surjective (algebraMap A Q))
  (P : C ⥤ ModuleCat.{u} Q) (B : ModuleCat.{u} Q)

def component (a : C) :
    (ModuleCat.restrictScalars (algebraMap A Q)).obj
      ((HomCoefficientFunctor.homPresheaf Q P B).obj a) ≅
    (HomCoefficientFunctor.homPresheaf A
      (P ⋙ ModuleCat.restrictScalars (algebraMap A Q))
      ((ModuleCat.restrictScalars (algebraMap A Q)).obj B)).obj a := by
  letI : IsScalarTower A Q ((ModuleCat.restrictScalars (algebraMap A Q)).obj B) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : IsScalarTower A Q ((ModuleCat.restrictScalars (algebraMap A Q)).obj (P.obj a)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (SurjectiveScalarHom.equiv A Q hQ
    ((ModuleCat.restrictScalars (algebraMap A Q)).obj B)
    ((ModuleCat.restrictScalars (algebraMap A Q)).obj (P.obj a))).toModuleIso

def iso :
    HomCoefficientFunctor.homPresheaf Q P B ⋙ ModuleCat.restrictScalars (algebraMap A Q) ≅
      HomCoefficientFunctor.homPresheaf A
        (P ⋙ ModuleCat.restrictScalars (algebraMap A Q))
        ((ModuleCat.restrictScalars (algebraMap A Q)).obj B) :=
  NatIso.ofComponents (component A Q hQ P B) (fun {_ _} _ => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    rfl)

@[simp] theorem hom_apply (a : C) (φ : B →ₗ[Q] P.obj a) (x : B) :
    (show ((ModuleCat.restrictScalars (algebraMap A Q)).obj B) →ₗ[A]
      ((ModuleCat.restrictScalars (algebraMap A Q)).obj (P.obj a)) from
        (iso A Q hQ P B).hom.app a φ) x = φ x := rfl

@[simp] theorem inv_apply (a : C)
    (φ : ((ModuleCat.restrictScalars (algebraMap A Q)).obj B) →ₗ[A]
      ((ModuleCat.restrictScalars (algebraMap A Q)).obj (P.obj a))) (x : B) :
    (show B →ₗ[Q] P.obj a from (iso A Q hQ P B).inv.app a φ) x = φ x := rfl

theorem evaluation (x : B) :
    (iso A Q hQ P B).hom ≫
      HomPresheafDualFrame.evaluation A
        (P ⋙ ModuleCat.restrictScalars (algebraMap A Q))
        ((ModuleCat.restrictScalars (algebraMap A Q)).obj B) x =
    Functor.whiskerRight (HomPresheafDualFrame.evaluation Q P B x)
      (ModuleCat.restrictScalars (algebraMap A Q)) := by
  apply NatTrans.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientScalarRestriction
