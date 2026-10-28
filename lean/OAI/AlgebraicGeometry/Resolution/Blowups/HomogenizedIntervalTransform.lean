import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HomogenizationTransform

/-! # Homogenized Interval Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizedIntervalTransform.Construction

noncomputable section

/-! An invariant comparison interval preserved by every actual permissible blowup step. -/

variable {R : Type*} [CommRing R]

theorem blowup_controlledTransform_mono_ideal
    (I : Ideal R) (a : I) (b : ℕ) {J L : Ideal R} (hJL : J ≤ L) :
    ControlledTransform.Construction.blowupControlledTransform I J b a ≤ ControlledTransform.Construction.blowupControlledTransform I L b a :=
  Submodule.colon_mono (Ideal.map_mono hJL) le_rfl

variable (k : Type*) [CommRing k] [Algebra k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Any center permissible for an intermediate homogenized ideal is
permissible for the original ideal, and the same comparison interval
holds for their actual controlled transforms. This invariant can be
carried through successive permissible blowups. -/
theorem relative_homogenized_interval_preserved
    (I J L : Ideal R) (a : I) (n : ℕ)
    (hJL : J ≤ L) (hLH : L ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (hL : L ≤ I ^ (n + 1)) :
    J ≤ I ^ (n + 1) ∧
      ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a ≤ ControlledTransform.Construction.blowupControlledTransform I L (n + 1) a ∧
      ControlledTransform.Construction.blowupControlledTransform I L (n + 1) a ≤
        Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n := by
  have hJ : J ≤ I ^ (n + 1) := hJL.trans hL
  exact ⟨hJ, blowup_controlledTransform_mono_ideal I a (n + 1) hJL,
    (blowup_controlledTransform_mono_ideal I a (n + 1) hLH).trans
      (Relative.HomogenizationTransform.Construction.relativeHomogenizedIdeal_controlledTransform_le k I J a n hJ)⟩

/-- After each such step, the two transformed ideals give exactly the
same allowable next centers, with the control unchanged. -/
theorem relative_homogenized_transform_center_iff
    (I J L : Ideal R) (a : I) (n : ℕ)
    (hJL : J ≤ L) (hLH : L ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (hL : L ≤ I ^ (n + 1))
    (Q : Ideal (Blowup.Charts.Construction.blowupChart I a)) :
    ControlledTransform.Construction.blowupControlledTransform I L (n + 1) a ≤ Q ^ (n + 1) ↔
      ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a ≤ Q ^ (n + 1) := by
  have h := relative_homogenized_interval_preserved k I J L a n hJL hLH hL
  exact Relative.DifferentialEquiv.Construction.relative_homogenized_interval_permissible_iff k Q _ _ n h.2.1 h.2.2

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizedIntervalTransform.Construction
