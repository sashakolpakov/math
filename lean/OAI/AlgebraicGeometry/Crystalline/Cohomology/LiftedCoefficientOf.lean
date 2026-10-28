import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientLarge

/-! # Lifted Coefficient Of -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientOf.LiftedCoefficientEquivalence

noncomputable section

/-! # Recover the original module from the prescribed two coefficient lifts -/

open _root_.CategoryTheory

universe u

variable (W : Type u) [CommRing W]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)

def restriction : ModuleCat.{u + 2} R ⥤ ModuleCat.{u + 2} W :=
  ModuleCat.restrictScalars (ULift.ringEquiv : R ≃+* W).symm.toRingHom

def upEquiv (M : ModuleCat.{u} W) :
    M ≃ₗ[W] (restriction W).obj ((LiftedCoefficientLarge.LiftedCoefficientTwist.lift W).obj M) where
  toFun x := ULift.up (ULift.up x)
  invFun x := x.down.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofIso {M : ModuleCat.{u} W} {N : ModuleCat.{u + 2} R}
    (e : (LiftedCoefficientLarge.LiftedCoefficientTwist.lift W).obj M ≅ N) :
    M ≃ₗ[W] (restriction W).obj N :=
  (upEquiv W M).trans ((restriction W).mapIso e).toLinearEquiv

theorem ofIso_apply {M : ModuleCat.{u} W} {N : ModuleCat.{u + 2} R}
    (e : (LiftedCoefficientLarge.LiftedCoefficientTwist.lift W).obj M ≅ N) (x : M) :
    ofIso W e x = e.hom (ULift.up (ULift.up x)) := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedCoefficientOf.LiftedCoefficientEquivalence
