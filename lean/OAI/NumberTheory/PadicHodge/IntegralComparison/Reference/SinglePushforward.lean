import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePresheafCoordinates

/-! # Single Pushforward -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePushforward

noncomputable section

/-! The original additive single-module coefficients commute with the
actual scheme pushforward through the canonical single-complex maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X Y : Scheme.{u}} (π : X ⟶ Y)

def presheaves : (X.Opensᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ (Y.Opensᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  (Functor.whiskeringLeft _ _ _).obj (TopologicalSpace.Opens.map π.base).op

instance presheaves_additive : (presheaves.{u,v} π).Additive := by
  dsimp only [presheaves]
  infer_instance

variable (N : X.Modules) (c : ℕ)

def coefficientIso :
    SinglePresheafCoordinates.presheaf ((Scheme.Modules.pushforward π).obj N) ≅
      (presheaves π).obj (SinglePresheafCoordinates.presheaf N) := Iso.refl _

def iso : Relative.AdditiveCechConcentration.coefficients
    ((single Y.Modules (.up ℕ) c).obj ((Scheme.Modules.pushforward π).obj N)) ≅
      ((presheaves π).mapHomologicalComplex (.up ℕ)).obj
        (Relative.AdditiveCechConcentration.coefficients ((single X.Modules (.up ℕ) c).obj N)) :=
  SinglePresheafCoordinates.iso ((Scheme.Modules.pushforward π).obj N) c ≪≫
    (single (Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℕ) c).mapIso (coefficientIso π N) ≪≫
      ((singleMapHomologicalComplex (presheaves π) (.up ℕ) c).app
        (SinglePresheafCoordinates.presheaf N)).symm ≪≫
      ((presheaves π).mapHomologicalComplex (.up ℕ)).mapIso
        (SinglePresheafCoordinates.iso N c).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePushforward
