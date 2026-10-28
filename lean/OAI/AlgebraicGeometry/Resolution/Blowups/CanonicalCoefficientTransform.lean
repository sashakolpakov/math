import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalCoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedHypersurfaceTransform

/-! # Canonical Coefficient Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalCoefficientTransform.Construction

noncomputable section

/-! Controlled transform bounds for the coefficient ideal defined using all derivations. -/

universe u

variable {R : Type u} [CommRing R]

/-- The actual coefficient-ideal transform on the divided hypersurface chart. -/
def canonicalCoefficientTransform (I J : Ideal R) (a z : I) (b : ℕ) :
    Ideal (Blowup.Charts.Construction.blowupChart I a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) :=
  ((CanonicalCoefficientIdeal.Construction.canonicalCoefficientIdeal z.val J b).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
    (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ b.factorial})

/-- Restriction to the divided hypersurface preserves the exact
exceptional factor of every permissible ambient ideal. -/
theorem blowup_hypersurface_ideal_factorization
    (I J : Ideal R) (a z : I) (n : ℕ) (hJ : J ≤ I ^ n) :
    (J.map (Ideal.Quotient.mk (Ideal.span {z.val}))).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z) =
      Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ n} *
      (ControlledTransform.Construction.blowupControlledTransform I J n a).map
        (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})) := by
  rw [Ideal.map_map]
  change J.map ((Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})).comp
    (Blowup.Charts.Construction.blowupChartConstants I a)) = _
  rw [← Ideal.map_map, ← ControlledTransform.Construction.blowup_controlledTransform_factorization I J n a hJ,
    Ideal.map_mul, Ideal.map_span, Set.image_singleton]
  rw [map_pow (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}))
    (Blowup.Charts.Construction.blowupChartConstants I a a.val) n]

/-- After quotienting the common exceptional power, the canonical
coefficient transform is exactly the weighted list of transformed full
differential ideals restricted to the new hypersurface. -/
theorem canonicalCoefficientTransform_eq_weighted
    (I J : Ideal R) (a z : I) (b : ℕ) (hJ : J ≤ I ^ b)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    canonicalCoefficientTransform I J a z b =
      WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j =>
        (ControlledTransform.Construction.blowupControlledTransform I (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J j.val) (b - j.val) a).map
          (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}))) := by
  unfold canonicalCoefficientTransform CanonicalCoefficientIdeal.Construction.canonicalCoefficientIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  rw [WeightedCoefficientTransform.Construction.weightedCoefficientIdeal_factorization _ b _ _ (fun j =>
    blowup_hypersurface_ideal_factorization I (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J j.val) a z (b - j.val)
      (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J (b - j.val) j.val
        (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ)))]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ (hc.pow b.factorial)

/-- The transformed canonical coefficient ideal is bounded above by
the canonical ideal of the transformed ambient ideal. -/
theorem canonicalCoefficientTransform_le_new_canonical
    (I J : Ideal R) (a z : I) (b : ℕ) (hJ : J ≤ I ^ b)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    canonicalCoefficientTransform I J a z b ≤
      CanonicalCoefficientIdeal.Construction.canonicalCoefficientIdeal (ExceptionalIdeal.Construction.blowupChartRatio I a z) (ControlledTransform.Construction.blowupControlledTransform I J b a) b := by
  rw [canonicalCoefficientTransform_eq_weighted I J a z b hJ hc]
  unfold WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal CanonicalCoefficientIdeal.Construction.canonicalCoefficientIdeal
  apply iSup_mono
  intro j
  apply pow_le_pow_left'
  apply Ideal.map_mono
  have hdiff := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_controlledTransform_le I J a (b - j.val) j.val
    (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ)
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hdiff

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalCoefficientTransform.Construction
