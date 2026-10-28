import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientTerminalBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv

/-! # Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Bound.Construction

noncomputable section

/-! Retained coefficient bounds control freshly homogenized coefficients and detect terminal ambient charts. -/

section

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem relativeCoefficientIdeal_mono (z : R) (b : ℕ) {J L : Ideal R} (h : J ≤ L) :
    Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z L b := by
  unfold Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal
  exact iSup_mono (fun j => pow_le_pow_left'
    (Ideal.map_mono (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k j.val h)) _)

theorem retained_coefficient_bound_to_homogenized (z : R) (J : Ideal R) (n m : ℕ)
    (C : Ideal (R ⧸ Ideal.span {z})) (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1))
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C m = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤ := by
  have hle := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k m
    (hupp.trans (relativeCoefficientIdeal_mono k z (n + 1) (Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n)))
  rw [hbound] at hle
  exact top_le_iff.mp hle

end

variable (k : Type*) {R : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing R] [Algebra k R] [Algebra.Smooth k R]

theorem retained_coefficient_bound_below_control_terminal
    (z : R) (J : Ideal R) (n m : ℕ) (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (C : Ideal (R ⧸ Ideal.span {z})) (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1))
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C m = ⊤) (hm : m < (n + 1).factorial) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤ := by
  apply Blowups.Smooth.CoefficientTerminalBound.Construction.retracted_coefficient_terminal_bound_clears_order k z J n hz (RingEquiv.refl _) C hupp
  change Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map (RingHom.id _)) ((n + 1).factorial - 1) = ⊤
  rw [Ideal.map_id]
  have hle := UnitCriterion.Construction.iteratedRelativeDifferentialIdeal_monotone_order k C
    (show m ≤ (n + 1).factorial - 1 by omega)
  rw [hbound] at hle
  exact top_le_iff.mp hle

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Bound.Construction
