import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.SingleAdditiveCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SinglePresheafCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafSingleIndexedCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureIndexedCoordinates

/-! # Single Global Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SingleGlobalCoordinates

noncomputable section

/-! The original native single-degree coordinate is the literal
presheaf-single coordinate after the canonical additive comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} [X.IsSeparated] (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (V : ι → X.Opens) (N : X.Modules) (c g q : ℕ) (hq : q=g+c)

def changeIso := HomologicalComplex₂.total.mapIso
  (SinglePresheafCoordinates.bicomplexIso N c (OrderedCech.Functor.Projection.functor V)) (.up ℕ)

omit [X.IsSeparated] in
theorem comparison :
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
      (SinglePresheafCoordinates.moduleSingle N c) q).hom ≫
      homologyMap (changeIso V N c).hom q ≫
        (Principal.PresheafSingleIndexedCoordinates.targetIso
          (SinglePresheafCoordinates.presheaf N) c g V q hq).hom =
    (Global.PureIndexedCoordinates.singleIso π V N c g q hq).hom ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso π V N g).hom := by
  subst q
  simp only [Principal.PresheafSingleIndexedCoordinates.targetIso,
    Global.PureIndexedCoordinates.singleIso, eqToIso_refl, Iso.refl_trans, Functor.mapIso_hom]
  dsimp only [changeIso]
  erw [SinglePresheafCoordinates.coordinates]
  exact IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.comparison π V N c g

omit [X.IsSeparated] in
theorem inverse :
    homologyMap (changeIso V N c).hom q ≫
      (Principal.PresheafSingleIndexedCoordinates.targetIso
        (SinglePresheafCoordinates.presheaf N) c g V q hq).hom ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso π V N g).inv =
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
      (SinglePresheafCoordinates.moduleSingle N c) q).inv ≫
        (Global.PureIndexedCoordinates.singleIso π V N c g q hq).hom := by
  have h := congrArg (fun f =>
    (IntrinsicOrdered.CechAdditiveCoordinates.Intrinsic.homologyIso π V
      (SinglePresheafCoordinates.moduleSingle N c) q).inv ≫ f ≫
      (IntrinsicOrdered.SingleAdditiveCoordinates.Intrinsic.coefficientIso π V N g).inv)
    (comparison π V N c g q hq)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.SingleGlobalCoordinates
