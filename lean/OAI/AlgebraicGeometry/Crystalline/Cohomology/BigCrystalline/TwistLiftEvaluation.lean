import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistSheafTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ScalarRestricted

/-! # Twist Lift Evaluation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistLiftEvaluation.BigCrystallineTwistLiftEvaluation

noncomputable section

/-! # Pointwise evaluation of the actual coefficient-twist lift on arbitrary presheaf maps -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base'
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W

theorem apply (P : Dᵒᵖ ⥤ ModuleCat.{u} W) (Q : Cᵒᵖ ⥤ ModuleCat.{u} W)
    (f : (TwistResolution.BigCrystallineTwistResolution.restriction p W A J δ base base' e he h).obj P ⟶ Q)
    (V : Cᵒᵖ) (z : P.obj ((tw).op.obj V)) :
    ScalarRestricted.ScalarRestrictedAdditiveMap.map (M := (E).obj (P.obj ((tw).op.obj V))) (N := (E).obj (Q.obj V))
      (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
      (((TwistSheafTransport.BigCrystallineTwistSheafTransport.liftedIso p W A J δ base base' e he h).hom.app P ≫
        Functor.whiskerRight f E).app V) (ULift.up z) =
    ULift.up (ScalarRestricted.ScalarRestrictedAdditiveMap.map (M := P.obj ((tw).op.obj V)) (N := Q.obj V)
      e.symm.toRingHom (f.app V) z) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistLiftEvaluation.BigCrystallineTwistLiftEvaluation
