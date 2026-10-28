import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Hypersurface Persistence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HypersurfacePersistence.Construction

noncomputable section

/-! Persistence of a maximal-contact equation in the intrinsic relative differential filtration. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

attribute [local instance] DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The divided hypersurface equation remains in the relative
control-one differential ideal after the actual blowup. -/
theorem blowupChart_relative_hypersurface_persists
    (I J : Ideal R) (a z : I) (n : ℕ) (hJ : J ≤ I ^ (n + 1))
    (hz : z.val ∈ DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    ExceptionalIdeal.Construction.blowupChartRatio I a z ∈
      DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n := by
  have h := DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_controlledTransform_le k I J a 1 n
    (by simpa only [Nat.add_comm 1 n] using hJ)
  apply (by simpa only [Nat.add_comm 1 n] using h)
  apply Ideal.mem_colon_span_singleton.mpr
  change ExceptionalIdeal.Construction.blowupChartRatio I a z * Blowup.Charts.Construction.blowupChartConstants I a a.val ^ 1 ∈
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (Blowup.Charts.Construction.blowupChartConstants I a)
  rw [pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val),
    mul_comm (ExceptionalIdeal.Construction.blowupChartRatio I a z) (Blowup.Charts.Construction.blowupChartConstants I a a.val),
    ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio]
  exact Ideal.mem_map_of_mem _ hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HypersurfacePersistence.Construction
