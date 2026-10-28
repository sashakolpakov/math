import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.FixedControlDrop

/-! # Fixed Control Drop -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FixedControlDrop.Construction

noncomputable section

/-! Strict fixed-control order drop on every actual chart of an isomorphic tangent-center blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- All denominator charts retain the original coefficient field and lower
the differential bound while dividing by the same prescribed positive control. -/
theorem isIso_blowup_fixed_control_drop (I J : Ideal R) [IsIso (ReesGrading.Construction.affineBlowupToSpec I)]
    (a : I) (n b : ℕ) (hb : 0 < b)
    (hcenter : I = Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) (hperm : J ≤ I ^ b)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (n + 1) = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J b a) n = ⊤ := by
  have hfact : J.map (Blowup.Charts.Construction.blowupChartConstants I a) =
      (I.map (Blowup.Charts.Construction.blowupChartConstants I a)) ^ b * ControlledTransform.Construction.blowupControlledTransform I J b a := by
    rw [ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.span_singleton_pow]
    exact (ControlledTransform.Construction.blowup_controlledTransform_factorization I J b a hperm).symm
  exact Etale.FixedControlDrop.Construction.smooth_etale_intrinsic_product_order_drop_hom k (Blowup.Charts.Construction.blowupChartConstants I a)
    (IsomorphicBlowupChartEtale.Construction.blowupChartConstants_etale_of_isIso I a) (fun _ => rfl)
    I J (ControlledTransform.Construction.blowupControlledTransform I J b a) n b hb hcenter hfact hbound

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.FixedControlDrop.Construction
