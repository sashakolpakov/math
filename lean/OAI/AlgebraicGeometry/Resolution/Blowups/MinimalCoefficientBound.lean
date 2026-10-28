import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBounds
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Bound
import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationTangent

/-! # Minimal Coefficient Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Least coefficient bounds distinguish terminal order from a nonempty next coefficient center. -/

universe u

theorem Component.CenterChoice.Construction.ComponentCenterChoice.terminal_of_bound_lt_factorial
    {k R : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing R] [Algebra k R] [Algebra.Smooth k R] {J : Ideal R} {n m : ℕ}
    (C : Component.CenterChoice.Construction.ComponentCenterChoice k R J n) (hb : C.HasBound m) (hm : m < (n + 1).factorial) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤ := by
  cases C with
  | terminal ht => exact ht
  | normal z D hD hz =>
      have hzH : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n := by
        rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
      have h := Coefficient.Bound.Construction.retained_coefficient_bound_below_control_terminal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n)
        n m hzH (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) le_rfl hb hm
      rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent] at h

theorem Component.CenterChoice.Construction.ComponentCenterChoice.tangentChoice_center_eq_top_iff
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {J : Ideal R} {n ℓ : ℕ}
    (C : Component.CenterChoice.Construction.ComponentCenterChoice k R J n) (h : C.HasBound (ℓ + 1)) :
    (C.toSurfaceTangentChoice ℓ h).center = ⊤ ↔ C.HasBound ℓ := by
  cases C with
  | terminal _ => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | normal z D hD hz =>
      change Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ = ⊤ ↔ _
      constructor
      · intro ht
        have he := Coefficient.TangentNaturality.Construction.coefficientTangentCenter_quotient k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
        rw [ht, Ideal.map_top] at he
        exact he.symm
      · intro hb
        change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k _ ℓ).comap _ = ⊤
        rw [hb, Ideal.comap_top]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
