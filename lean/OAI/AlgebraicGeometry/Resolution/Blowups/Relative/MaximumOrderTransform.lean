import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.MaximumOrderTransform

/-! # Maximum Order Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.MaximumOrderTransform.Construction

noncomputable section

/-! The original base-relative order bound persists on every actual blowup chart. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

attribute [local instance] DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem blowup_preserves_relative_differential_order_bound
    (I J : Ideal R) (a : I) (b : ℕ) (hJ : J ≤ I ^ b)
    (hbound : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J b = ⊤) :
    DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J b a) b = ⊤ := by
  have h := DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_controlledTransform_le k I J a 0 b
    (by simpa only [zero_add] using hJ)
  rw [zero_add, hbound, ResidualCoefficientTransform.Construction.blowupControlledTransform_zero, Ideal.map_top] at h
  exact top_le_iff.mp h

theorem blowup_preserves_relative_bound_at_all_primes
    (I J : Ideal R) (a : I) (b : ℕ) (hJ : J ≤ I ^ b)
    (hbound : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J b = ⊤)
    (q : Ideal (Blowup.Charts.Construction.blowupChart I a)) [q.IsPrime] :
    ¬ MaximumOrderTransform.Construction.idealHasLocalOrderAtLeast (ControlledTransform.Construction.blowupControlledTransform I J b a) q (b + 1) := by
  have h := DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k
    (ControlledTransform.Construction.blowupControlledTransform I J b a) b
  rw [blowup_preserves_relative_differential_order_bound k I J a b hJ hbound] at h
  exact DifferentialLocalBound.Construction.local_order_lt_of_differential_top _ b (top_le_iff.mp h) q

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.MaximumOrderTransform.Construction
