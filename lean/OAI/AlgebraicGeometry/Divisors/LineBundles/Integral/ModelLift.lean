import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IntegralModelLift

/-! # Model Lift -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ModelLift.BundleCycles.IntegralModelLift

noncomputable section

/-! Integral elements of a model embed in any integrally closed local
ring containing the base and sharing the specified fraction field. -/

variable (R A B L : Type*) [CommRing R] [CommRing A] [CommRing B] [Field L]
  [Algebra R A] [Algebra R B] [Algebra R L] [Algebra A L] [Algebra B L]
  [IsScalarTower R A L] [IsScalarTower R B L]
  [IsIntegrallyClosed B] [IsFractionRing B L] [Algebra.IsIntegral R A]

include R

theorem exists_lift_element (a : A) : ∃ b : B, algebraMap B L b = algebraMap A L a := by
  exact (isIntegrallyClosed_iff L).mp ‹IsIntegrallyClosed B›
    ((Algebra.IsIntegral.isIntegral (R := R) a).algebraMap (B := L)).tower_top

def lift : A →+* B where
  toFun a := (exists_lift_element R A B L a).choose
  map_one' := by
    apply IsFractionRing.injective B L
    rw [(exists_lift_element R A B L 1).choose_spec, map_one, map_one]
  map_zero' := by
    apply IsFractionRing.injective B L
    rw [(exists_lift_element R A B L 0).choose_spec, map_zero, map_zero]
  map_add' a b := by
    apply IsFractionRing.injective B L
    rw [(exists_lift_element R A B L (a + b)).choose_spec, map_add, map_add,
      (exists_lift_element R A B L a).choose_spec, (exists_lift_element R A B L b).choose_spec]
  map_mul' a b := by
    apply IsFractionRing.injective B L
    rw [(exists_lift_element R A B L (a * b)).choose_spec, map_mul, map_mul,
      (exists_lift_element R A B L a).choose_spec, (exists_lift_element R A B L b).choose_spec]

theorem algebraMap_lift (a : A) :
    algebraMap B L (lift R A B L a) = algebraMap A L a :=
  (exists_lift_element R A B L a).choose_spec

theorem lift_algebraMap (r : R) : lift R A B L (algebraMap R A r) = algebraMap R B r := by
  apply IsFractionRing.injective B L
  rw [algebraMap_lift, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ModelLift.BundleCycles.IntegralModelLift
