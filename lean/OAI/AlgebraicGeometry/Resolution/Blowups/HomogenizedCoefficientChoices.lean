import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalComponent.Homogenization

/-! # Homogenized Coefficient Choices -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Homogenization preserves every finite coefficient-bound ideal of a chosen normal. -/

universe u

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {J : Ideal R} {n : ℕ}

theorem Component.CenterChoice.Construction.ComponentCenterChoice.homogenize_boundIdeal (C : Component.CenterChoice.Construction.ComponentCenterChoice k R J n) (m : ℕ) :
    C.homogenize.boundIdeal m = C.boundIdeal m := by
  cases C with
  | terminal _ => rfl
  | normal z D hD hz =>
      change Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n) (n + 1) m = _
      rw [HomogenizationIdempotence.Construction.relativeHomogenizedIdeal_idempotent]
      rfl

theorem Component.CenterChoice.Construction.ComponentCenterChoice.homogenize_hasBound_iff (C : Component.CenterChoice.Construction.ComponentCenterChoice k R J n) (m : ℕ) :
    C.homogenize.HasBound m ↔ C.HasBound m := by
  rw [← C.homogenize.boundIdeal_eq_top_iff m, C.homogenize_boundIdeal m, C.boundIdeal_eq_top_iff m]

theorem Component.CenterChoice.Construction.ComponentCenterChoice.homogenize_surfaceChoice_center (C : Component.CenterChoice.Construction.ComponentCenterChoice k R J n) (ℓ : ℕ)
    (h : C.HasBound (ℓ + 1)) (hh : C.homogenize.HasBound (ℓ + 1)) :
    (C.homogenize.toSurfaceTangentChoice ℓ hh).center = (C.toSurfaceTangentChoice ℓ h).center := by
  cases C with
  | terminal _ => rfl
  | normal z D hD hz =>
      change Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n) (n + 1) ℓ = _
      rw [HomogenizationIdempotence.Construction.relativeHomogenizedIdeal_idempotent]
      rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups
