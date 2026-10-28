import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointChartTransport

/-! # Controlled Power Scaling -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ControlledPowerScaling.Construction

noncomputable section

/-! Exact control scaling by positive powers, on actual ideals and Rees charts. -/

variable {R : Type*} [CommRing R]

/-- Taking an ideal power and multiplying the control commute exactly
with the actual controlled transform at any permissible center. -/
theorem blowupControlledTransform_pow (I J : Ideal R) (a : I) (b e : ℕ)
    (hJ : J ≤ I ^ b) :
    ControlledTransform.Construction.blowupControlledTransform I (J ^ e) (b * e) a = (ControlledTransform.Construction.blowupControlledTransform I J b a) ^ e := by
  change ((J ^ e).map (Blowup.Charts.Construction.blowupChartConstants I a)).colon
    (Ideal.span {Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (b * e)}) = _
  rw [Ideal.map_pow, ← ControlledTransform.Construction.blowup_controlledTransform_factorization I J b a hJ,
    mul_pow, Ideal.span_singleton_pow, ← pow_mul (Blowup.Charts.Construction.blowupChartConstants I a a.val) b e]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _
    ((ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).pow (b * e))

variable (k : Type*) [Field k] [CharZero k] [IsAlgClosed k]
  [Algebra k R] [Algebra.Smooth k R]

/-- Positive power scaling preserves the terminal marked-order condition
on every smooth affine algebra, without a chosen polynomial coordinate frame. -/
theorem smooth_relative_terminal_power_iff (J : Ideal R) (b e : ℕ) (hb : 0 < b) (he : 0 < e) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J ^ e) (b * e - 1) = ⊤ ↔
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (b - 1) = ⊤ := by
  rw [Blowups.Smooth.ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k (J ^ e) (b * e - 1),
    Blowups.Smooth.ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k J (b - 1)]
  simp only [Nat.sub_add_cancel (Nat.mul_pos hb he), Nat.sub_add_cancel hb,
    ClosedWeightedOrder.Construction.closedPoint_local_order_iff]
  constructor
  · intro h q hq hJ
    apply h q
    simpa only [pow_mul] using pow_le_pow_left' hJ e
  · intro h q hq hJ
    exact h q (Blowups.Smooth.ClosedPointPowerRoot.Construction.smooth_closedPoint_ideal_power_root k J q b e he hJ)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ControlledPowerScaling.Construction
