import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme

/-! # Linear Integral Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearIntegralAction

noncomputable section

/-! A complex-linear ring action preserving the actual exponential
lattice algebraizes to an integral action on the original abelian scheme.
Faithfulness of the original linear lifts proves every ring law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false

namespace IntrinsicLinearMaps

variable {R : Type*} [CommRing R] (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
  (ρ : R →+* Module.End ℂ (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))
  (hρ : ∀ a x, x ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A → ρ a x ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)

def integralActionOfNativeLinear : ActionData.IntegralAction R (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) where
  map a := LinearDescent.IntrinsicLinearMaps.nativeLinearDescend (ρ a) (hρ a)
  preservesGroup a := inferInstance
  map_zero := by
    apply Maps.IntrinsicLinearMaps.linearLift_faithful
    rw [LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend, Maps.IntrinsicLinearMaps.linearLift_zero, ρ.map_zero]
  map_one := by
    change LinearDescent.IntrinsicLinearMaps.nativeLinearDescend (ρ 1) (hρ 1) = 𝟙 A.toOver
    apply Maps.IntrinsicLinearMaps.linearLift_faithful
    rw [LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend, Maps.IntrinsicLinearMaps.linearLift_id, ρ.map_one]
    rfl
  map_add a b := by
    change LinearDescent.IntrinsicLinearMaps.nativeLinearDescend (ρ (a + b)) (hρ (a + b)) =
      LinearDescent.IntrinsicLinearMaps.nativeLinearDescend (ρ a) (hρ a) * LinearDescent.IntrinsicLinearMaps.nativeLinearDescend (ρ b) (hρ b)
    apply Maps.IntrinsicLinearMaps.linearLift_faithful
    rw [Maps.IntrinsicLinearMaps.linearLift_add, LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend,
      LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend, LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend, ρ.map_add]
  map_mul a b := by
    apply Maps.IntrinsicLinearMaps.linearLift_faithful
    rw [Maps.IntrinsicLinearMaps.linearLift_comp, LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend,
      LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend, LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend, ρ.map_mul]
    rfl

theorem integralActionOfNativeLinear_lift (a : R) :
    Maps.IntrinsicLinearMaps.linearLift ((integralActionOfNativeLinear A ρ hρ).map a) = ρ a :=
  LinearDescent.IntrinsicLinearMaps.linearLift_nativeLinearDescend (ρ a) (hρ a)

end IntrinsicLinearMaps

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LinearIntegralAction
