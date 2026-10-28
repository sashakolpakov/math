import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.CoordinateIdeal
import Mathlib.RingTheory.Localization.Algebra

/-! # Principal Open Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.PrincipalOpenLift.Construction

noncomputable section

/-! Surjective normal quotients commute exactly with corresponding principal ambient opens. -/

universe u

variable {k R Q : Type u} [CommRing k] [CommRing R] [CommRing Q]
  [Algebra k R] [Algebra k Q]

def quotientPrincipalOpenMap (q : R →ₐ[k] Q) (r : R) :
    Localization.Away r →ₐ[k] Localization.Away (q r) := by
  have h : Submonoid.powers r ≤ (Submonoid.powers (q r)).comap q.toRingHom := by
    change Submonoid.powers r ≤ (Submonoid.powers (q.toRingHom r)).comap q.toRingHom
    rw [← Submonoid.map_powers q.toRingHom r]
    exact Submonoid.le_comap_map _
  let φ : Localization.Away r →+* Localization.Away (q r) :=
    IsLocalization.map (Localization.Away (q r)) q.toRingHom h
  have hφ (x : R) : φ (algebraMap R (Localization.Away r) x) =
      algebraMap Q (Localization.Away (q r)) (q x) := IsLocalization.map_eq h x
  refine { __ := φ, commutes' := ?_ }
  intro c
  change φ (algebraMap k (Localization.Away r) c) = _
  rw [IsScalarTower.algebraMap_apply k R (Localization.Away r), hφ,
    q.commutes, ← IsScalarTower.algebraMap_apply k Q (Localization.Away (q r))]

theorem quotientPrincipalOpenMap_constants (q : R →ₐ[k] Q) (r x : R) :
    quotientPrincipalOpenMap q r (algebraMap R (Localization.Away r) x) =
      algebraMap Q (Localization.Away (q r)) (q x) := by
  apply IsLocalization.map_eq (M := Submonoid.powers r) (T := Submonoid.powers (q r))
  change Submonoid.powers r ≤ (Submonoid.powers (q.toRingHom r)).comap q.toRingHom
  rw [← Submonoid.map_powers q.toRingHom r]
  exact Submonoid.le_comap_map _

theorem quotientPrincipalOpenMap_surjective (q : R →ₐ[k] Q) (hq : Function.Surjective q) (r : R) :
    Function.Surjective (quotientPrincipalOpenMap q r) := by
  let : IsLocalization ((Submonoid.powers r).map q.toRingHom) (Localization.Away (q r)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact IsLocalization.map_surjective_of_surjective (Submonoid.powers r)
    (Localization.Away r) (Localization.Away (q r)) hq

theorem quotientPrincipalOpenMap_kernel (q : R →ₐ[k] Q) (r : R) :
    RingHom.ker (quotientPrincipalOpenMap q r).toRingHom =
      (RingHom.ker q.toRingHom).map (algebraMap R (Localization.Away r)) := by
  exact IsLocalization.ker_map (S := Localization.Away r) (Localization.Away (q r)) q.toRingHom
    (Submonoid.map_powers q.toRingHom r)

theorem quotientPrincipalOpenMap_center (q : R →ₐ[k] Q) (hq : Function.Surjective q)
    (r : R) (K : Ideal Q) :
    (K.comap q.toRingHom).map (algebraMap R (Localization.Away r)) =
      (K.map (algebraMap Q (Localization.Away (q r)))).comap
        (quotientPrincipalOpenMap q r).toRingHom := by
  apply CoordinateIdeal.Construction.quotient_center_map_of_surjective_kernel_square q.toRingHom
    (quotientPrincipalOpenMap q r).toRingHom (algebraMap R (Localization.Away r))
    (algebraMap Q (Localization.Away (q r))) hq (quotientPrincipalOpenMap_surjective q hq r)
  · ext x
    exact quotientPrincipalOpenMap_constants q r x
  · exact quotientPrincipalOpenMap_kernel q r

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.PrincipalOpenLift.Construction
