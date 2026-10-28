import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveOrder

/-! # DVR Pencil Poles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DVRPencilPoles

noncomputable section

/-! Translating a rational parameter by a regular local function does
not change its polar multiplicity in a discrete valuation ring. -/

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

theorem order_nonneg_of_valuation_le_one (g : K) (hg : g ≠ 0)
    (hv : (IsDiscreteValuationRing.maximalIdeal R).valuation K g ≤ 1) :
    0 ≤ WithZero.log (Ring.ordFrac R g) := by
  have hn : (IsDiscreteValuationRing.maximalIdeal R).valuation K g ≠ 0 := (map_ne_zero _).mpr hg
  rw [Ring.ordFrac_eq_valuation_inv]
  apply (WithZero.le_log_iff_exp_le (inv_ne_zero hn)).mpr
  simpa only [WithZero.exp_zero] using (one_le_inv₀ (zero_lt_iff.mpr hn)).mpr hv

theorem negative_part_sub (g : K) (hg : g ≠ 0) (a : R) (hga : g - algebraMap R K a ≠ 0) :
    max (-WithZero.log (Ring.ordFrac R (g - algebraMap R K a))) 0 =
      max (-WithZero.log (Ring.ordFrac R g)) 0 := by
  let v := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  have ha : v (algebraMap R K a) ≤ 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ a
  by_cases hvg : v g ≤ 1
  · have hva : v (g - algebraMap R K a) ≤ 1 := (v.map_sub _ _).trans (max_le hvg ha)
    have hg0 := order_nonneg_of_valuation_le_one R K g hg hvg
    have hga0 := order_nonneg_of_valuation_le_one R K (g - algebraMap R K a) hga hva
    rw [max_eq_right (neg_nonpos.mpr hga0), max_eq_right (neg_nonpos.mpr hg0)]
  · have hv : v (g - algebraMap R K a) = v g := v.map_sub_eq_of_lt_left (ha.trans_lt (lt_of_not_ge hvg))
    rw [Ring.ordFrac_eq_valuation_inv, Ring.ordFrac_eq_valuation_inv]
    exact congrArg (fun z => max (-WithZero.log z⁻¹) 0) hv

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DVRPencilPoles
