import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalCoefficientTransform

/-! # Coefficient Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientTransform.Construction

noncomputable section

/-! Controlled transforms of the intrinsic coefficient ideals that agree on étale overlaps. -/

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

attribute [local instance] DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def relativeCoefficientTransform (I J : Ideal R) (a z : I) (b : ℕ) :
    Ideal (Blowup.Charts.Construction.blowupChart I a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) :=
  ((CoefficientIdeal.Construction.relativeCoefficientIdeal k z.val J b).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
    (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ b.factorial})

/-- The relative coefficient transform is exactly the weighted family
of transformed relative differential ideals on the divided hypersurface. -/
theorem relativeCoefficientTransform_eq_weighted
    (I J : Ideal R) (a z : I) (b : ℕ) (hJ : J ≤ I ^ b)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    relativeCoefficientTransform k I J a z b =
      WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j =>
        (ControlledTransform.Construction.blowupControlledTransform I (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val) (b - j.val) a).map
          (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}))) := by
  unfold relativeCoefficientTransform CoefficientIdeal.Construction.relativeCoefficientIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  rw [WeightedCoefficientTransform.Construction.weightedCoefficientIdeal_factorization _ b _ _ (fun j =>
    CanonicalCoefficientTransform.Construction.blowup_hypersurface_ideal_factorization I (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val) a z
      (b - j.val) ((DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J j.val).trans
        (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J (b - j.val) j.val
          (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ))))]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ (hc.pow b.factorial)

/-- The transform is bounded by the intrinsic relative coefficient
ideal of the transformed ambient ideal, over the same coefficient ring. -/
theorem relativeCoefficientTransform_le_new_relative
    (I J : Ideal R) (a z : I) (b : ℕ) (hJ : J ≤ I ^ b)
    (hc : IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))) :
    relativeCoefficientTransform k I J a z b ≤
      CoefficientIdeal.Construction.relativeCoefficientIdeal k (ExceptionalIdeal.Construction.blowupChartRatio I a z) (ControlledTransform.Construction.blowupControlledTransform I J b a) b := by
  rw [relativeCoefficientTransform_eq_weighted k I J a z b hJ hc]
  unfold WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal CoefficientIdeal.Construction.relativeCoefficientIdeal
  apply iSup_mono
  intro j
  apply pow_le_pow_left'
  apply Ideal.map_mono
  have hdiff := DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_controlledTransform_le k I J a (b - j.val) j.val
    (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ)
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hdiff

theorem weightedCoefficientTransform_le_relative
    (I J : Ideal R) (a z : I) (D : Derivation k R R) (b : ℕ) :
    ((ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal D z.val J b).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ b.factorial}) ≤
      relativeCoefficientTransform k I J a z b :=
  Submodule.colon_mono (Ideal.map_mono (CoefficientIdeal.Construction.weightedDifferentialCoefficientIdeal_le_relative k D z.val J b))
    le_rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientTransform.Construction
