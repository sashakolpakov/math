import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Divisor

/-! # Integral Model Lift -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IntegralModelLift.Normalization

/-!
# ProjectionFormula: normalization at codimension-one affine local rings

The normal ring and the finite-colength hypothesis are obtained from the
actual integral closure. No regularity of the original local ring is used.
-/

theorem isDedekindDomain_integralClosure
    (R K : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Module.Finite R (integralClosure R K)] :
    IsDedekindDomain (integralClosure R K) := by
  let : Ring.DimensionLEOne R :=
    ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  let : IsNoetherianRing (integralClosure R K) :=
    IsNoetherianRing.of_finite R (integralClosure R K)
  let : IsIntegrallyClosed (integralClosure R K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) K
  exact
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }

/-- The order-length comparison on the actual finite normalization of a
one-dimensional localization of an affine characteristic-zero domain. -/
theorem ord_eq_normalization_length
    (k B R K : Type*) [Field k] [CharZero k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B]
    [CommRing R] [IsDomain R] [Algebra B R]
    (M : Submonoid B) [IsLocalization M R]
    [Ring.KrullDimLE 1 R] [Field K] [Algebra B K] [Algebra R K]
    [IsScalarTower B R K] [IsFractionRing B K] [IsFractionRing R K]
    (a : R) (ha : a ≠ 0) :
    Ring.ord R a = Module.length R
      ((integralClosure R K) ⧸ Ideal.span {algebraMap R (integralClosure R K) a}) := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let : IsNoetherianRing R := IsLocalization.isNoetherianRing M R inferInstance
  let : Module.Finite R (integralClosure R K) :=
    ProjectionFormula.Finite.Normalization.finite_integralClosure_localization k B R K M
  let : IsFractionRing (integralClosure R K) K :=
    integralClosure.isFractionRing_of_finite_extension K K
  exact ProjectionFormula.Finite.Colength.ord_eq_length_birational_extension
    R (integralClosure R K) K a ha

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IntegralModelLift.Normalization

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IntegralModelLift

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

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IntegralModelLift

end

end OAI
