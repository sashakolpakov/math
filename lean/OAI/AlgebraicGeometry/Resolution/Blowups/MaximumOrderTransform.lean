import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialLocalBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder

/-! # Maximum Order Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MaximumOrderTransform.Construction

noncomputable section

/-! Maximum-order bounds persist under actual controlled blowups. -/

variable {R : Type*} [CommRing R]

/-- Order at a prime is measured in the actual localization and its maximal ideal. -/
def idealHasLocalOrderAtLeast (J q : Ideal R) [q.IsPrime] (b : ℕ) : Prop :=
  J.map (algebraMap R (Localization.AtPrime q)) ≤
    IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b

/-- A differential unit-ideal bound is preserved when the ideal is
transformed at its bounded order. This holds on every actual Rees chart. -/
theorem blowup_preserves_differential_order_bound (I J : Ideal R) (a : I) (m : ℕ)
    (hJ : J ≤ I ^ m) (hbound : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J m = ⊤) :
    DifferentialIdealTransform.Construction.iteratedDifferentialIdeal (ControlledTransform.Construction.blowupControlledTransform I J m a) m = ⊤ := by
  have h := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_controlledTransform_le I J a 0 m
    (by simpa only [zero_add] using hJ)
  rw [zero_add, hbound, ResidualCoefficientTransform.Construction.blowupControlledTransform_zero, Ideal.map_top] at h
  exact top_le_iff.mp h

/-- The transformed order is bounded at every prime, including nonclosed points. -/
theorem blowup_preserves_maximum_order_at_all_primes (I J : Ideal R) (a : I) (m : ℕ)
    (hJ : J ≤ I ^ m) (hbound : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J m = ⊤)
    (q : Ideal (Blowup.Charts.Construction.blowupChart I a)) [q.IsPrime] :
    ¬ idealHasLocalOrderAtLeast (ControlledTransform.Construction.blowupControlledTransform I J m a) q (m + 1) :=
  DifferentialLocalBound.Construction.local_order_lt_of_differential_top _ m
    (blowup_preserves_differential_order_bound I J a m hJ hbound) q

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CharZero K] [CommRing S]
  [Fintype σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

include σ K in
/-- A uniform closed-point order bound is equivalent to the differential
unit-ideal condition, which can be transported through blowups. -/
theorem etale_differential_bound_iff_closedPoint_bound (J : Ideal S) (m : ℕ) :
    DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J m = ⊤ ↔
      ∀ (q : Ideal S) [q.IsMaximal],
        ¬ J.map (algebraMap S (Localization.AtPrime q)) ≤
          IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (m + 1) := by
  constructor
  · intro h q _
    exact DifferentialLocalBound.Construction.local_order_lt_of_differential_top J m h q
  · intro h
    by_contra hproper
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J m) hproper
    let : q.IsMaximal := hq
    exact h q ((Blowups.Etale.ClosedOrder.Construction.etale_closedPoint_order_iff_differentialIdeal (σ := σ) (K := K) J q m).mpr hle)

include σ K in
/-- An actual permissible blowup cannot increase a finite uniform order
bound when controlled at that bound. -/
theorem etale_blowup_order_does_not_increase (I J : Ideal S) (a : I) (m : ℕ)
    (hJ : J ≤ I ^ m)
    (hbound : ∀ (q : Ideal S) [q.IsMaximal],
      ¬ J.map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (m + 1))
    (q : Ideal (Blowup.Charts.Construction.blowupChart I a)) [q.IsPrime] :
    ¬ idealHasLocalOrderAtLeast (ControlledTransform.Construction.blowupControlledTransform I J m a) q (m + 1) :=
  blowup_preserves_maximum_order_at_all_primes I J a m hJ
    ((etale_differential_bound_iff_closedPoint_bound (σ := σ) (K := K) J m).mpr hbound) q

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MaximumOrderTransform.Construction
