import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialLocalBound
import OAI.AlgebraicGeometry.Resolution.Blowups.MaximumOrderTransform

/-! # Unit Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitBlowup.Construction

noncomputable section

/-! Unit coefficient transforms terminate actual ambient blowup charts. -/

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- If an intermediate coefficient ideal becomes the unit ideal after the
actual transform, the ambient differential ideal is the unit ideal on that chart. -/
theorem coefficient_unit_transform_clears_ambient
    (I J : Ideal R) (a z : I) (n : ℕ) (hJ : J ≤ I ^ (n + 1))
    (hz : z.val ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (C : Ideal (R ⧸ Ideal.span {z.val}))
    (hC : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z.val J (n + 1))
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val)))
    (hunit : (C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (n + 1).factorial}) = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n = ⊤ := by
  apply UnitCriterion.Construction.relative_coefficient_unit_forces_differential_unit k (ExceptionalIdeal.Construction.blowupChartRatio I a z)
    (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n
    (Relative.HypersurfacePersistence.Construction.blowupChart_relative_hypersurface_persists k I J a z n hJ hz)
  apply top_unique
  rw [← hunit]
  exact (Submodule.colon_mono (Ideal.map_mono hC) le_rfl).trans
    (Relative.CoefficientTransform.Construction.relativeCoefficientTransform_le_new_relative k I J a z (n + 1) hJ hc)

/-- The same termination holds at every prime of the actual chart. -/
theorem coefficient_unit_transform_clears_all_primes
    (I J : Ideal R) (a z : I) (n : ℕ) (hJ : J ≤ I ^ (n + 1))
    (hz : z.val ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (C : Ideal (R ⧸ Ideal.span {z.val}))
    (hC : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z.val J (n + 1))
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val)))
    (hunit : (C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (n + 1).factorial}) = ⊤)
    (q : Ideal (Blowup.Charts.Construction.blowupChart I a)) [q.IsPrime] :
    ¬ MaximumOrderTransform.Construction.idealHasLocalOrderAtLeast (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) q (n + 1) := by
  have hrel := coefficient_unit_transform_clears_ambient k I J a z n hJ hz C hC hc hunit
  have hord : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n = ⊤ := by
    apply top_unique
    rw [← hrel]
    exact Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k _ n
  exact DifferentialLocalBound.Construction.local_order_lt_of_differential_top _ n hord q

/-- The chart using the hypersurface equation itself as denominator is
already terminal: the persistent divided equation is one. -/
theorem relative_hypersurface_denominator_differential_unit
    (I J : Ideal R) (z : I) (n : ℕ) (hJ : J ≤ I ^ (n + 1))
    (hz : z.val ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) z) n = ⊤ := by
  have h := Relative.HypersurfacePersistence.Construction.blowupChart_relative_hypersurface_persists k I J z z n hJ hz
  rw [Etale.CoefficientStep.Construction.blowupChartRatio_self] at h
  exact Ideal.eq_top_of_isUnit_mem _ h isUnit_one

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitBlowup.Construction
