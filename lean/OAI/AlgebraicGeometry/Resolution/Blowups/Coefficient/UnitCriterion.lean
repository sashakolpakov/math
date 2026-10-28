import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HypersurfacePersistence

/-! # Unit Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion.Construction

noncomputable section

/-! A unit coefficient ideal clears the ambient differential ideal algebraically. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem iteratedRelativeDifferentialIdeal_monotone_order (J : Ideal R) :
    Monotone (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k n (Relative.DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k J)

/-- Every weighted coefficient belongs to the image of the control-one
relative differential ideal. -/
theorem relativeCoefficientIdeal_le_tangent_image (z : R) (J : Ideal R) (n : ℕ) :
    Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1) ≤
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (Ideal.Quotient.mk (Ideal.span {z})) := by
  unfold Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal
  apply iSup_le
  intro j
  have hp : 1 ≤ WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) j := Nat.succ_le_of_lt (WeightedCoefficientIdeal.Construction.coefficientWeight_pos (n + 1) j)
  calc
    ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
        WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) j ≤
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map (Ideal.Quotient.mk (Ideal.span {z})) := by
        simpa only [pow_one] using (Ideal.pow_le_pow_right
          (I := (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map (Ideal.Quotient.mk (Ideal.span {z})))) hp
    _ ≤ _ := Ideal.map_mono (iteratedRelativeDifferentialIdeal_monotone_order k J
      (Nat.le_of_lt_succ j.isLt))

/-- If the persistent hypersurface's coefficient ideal is the unit ideal,
the ambient differential ideal is the unit ideal as well. No closed-point,
coordinate-presentation, or dimension hypothesis is needed for this implication. -/
theorem relative_coefficient_unit_forces_differential_unit (z : R) (J : Ideal R) (n : ℕ)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hC : Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1) = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤ := by
  let q := Ideal.Quotient.mk (Ideal.span {z})
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  have hmap : T.map q = ⊤ := by
    apply top_unique
    rw [← hC]
    exact relativeCoefficientIdeal_le_tangent_image k z J n
  have hker : RingHom.ker q ≤ T := by
    rw [Ideal.mk_ker]
    exact (Ideal.span_singleton_le_iff_mem T).mpr hz
  have h := Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective T
  rw [hmap, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion.Construction
