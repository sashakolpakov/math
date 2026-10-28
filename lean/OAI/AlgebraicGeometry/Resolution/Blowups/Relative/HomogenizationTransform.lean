import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Homogenization Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HomogenizationTransform.Construction

noncomputable section

/-! Homogenization bounds remain valid through actual permissible blowup charts. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

attribute [local instance] DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

def relativeHomogenizedTransformFamily (I J : Ideal R) (a : I) (n : ℕ) : Ideal (Blowup.Charts.Construction.blowupChart I a) :=
  ⨆ j : Fin (n + 1),
    ControlledTransform.Construction.blowupControlledTransform I (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val) (n + 1 - j.val) a *
      (ControlledTransform.Construction.blowupControlledTransform I (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) 1 a) ^ j.val

/-- The actual transform of homogenization is the sum of products of
the separately transformed differential and tangent ideals. -/
theorem relativeHomogenizedIdeal_controlledTransform_eq
    (I J : Ideal R) (a : I) (n : ℕ) (hJ : J ≤ I ^ (n + 1)) :
    ControlledTransform.Construction.blowupControlledTransform I (DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) a =
      relativeHomogenizedTransformFamily k I J a n := by
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  let T := DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  have hT : T ≤ I ^ 1 := (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J n).trans
    (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J 1 n (by simpa only [Nat.add_comm 1 n] using hJ))
  have hfactor (j : Fin (n + 1)) :
      (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val * T ^ j.val).map (Blowup.Charts.Construction.blowupChartConstants I a) =
        Ideal.span {c ^ (n + 1)} *
          (ControlledTransform.Construction.blowupControlledTransform I (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val) (n + 1 - j.val) a *
            (ControlledTransform.Construction.blowupControlledTransform I T 1 a) ^ j.val) := by
    have hD : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val ≤ I ^ (n + 1 - j.val) :=
      (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J j.val).trans
        (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J (n + 1 - j.val) j.val
          (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ))
    rw [Ideal.map_mul, Ideal.map_pow,
      ← ControlledTransform.Construction.blowup_controlledTransform_factorization I (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val)
        (n + 1 - j.val) a hD,
      ← ControlledTransform.Construction.blowup_controlledTransform_factorization I T 1 a hT,
      pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val), mul_pow, Ideal.span_singleton_pow,
      mul_mul_mul_comm, Ideal.span_singleton_mul_span_singleton,
      ← pow_add (Blowup.Charts.Construction.blowupChartConstants I a a.val), Nat.sub_add_cancel (Nat.le_of_lt j.isLt)]
  have htotal : (DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map (Blowup.Charts.Construction.blowupChartConstants I a) =
      Ideal.span {c ^ (n + 1)} * relativeHomogenizedTransformFamily k I J a n := by
    unfold DifferentialEquiv.Construction.relativeHomogenizedIdeal relativeHomogenizedTransformFamily
    rw [Ideal.map_iSup, Ideal.mul_iSup]
    apply congrArg iSup
    funext j
    exact hfactor j
  change ((DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map (Blowup.Charts.Construction.blowupChartConstants I a)).colon
    (Ideal.span {c ^ (n + 1)}) = _
  rw [htotal]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _
    (IsRegular.pow (a := c) (n + 1) (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a))

/-- The transformed homogenized ideal stays below the homogenization
of the transformed original ideal. -/
theorem relativeHomogenizedIdeal_controlledTransform_le
    (I J : Ideal R) (a : I) (n : ℕ) (hJ : J ≤ I ^ (n + 1)) :
    ControlledTransform.Construction.blowupControlledTransform I (DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) a ≤
      DifferentialEquiv.Construction.relativeHomogenizedIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n := by
  rw [relativeHomogenizedIdeal_controlledTransform_eq k I J a n hJ]
  unfold relativeHomogenizedTransformFamily DifferentialEquiv.Construction.relativeHomogenizedIdeal
  apply iSup_mono
  intro j
  apply Ideal.mul_mono
  · have h := DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_controlledTransform_le k I J a
      (n + 1 - j.val) j.val
      (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ)
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using h
  · apply pow_le_pow_left'
    have h := DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_controlledTransform_le k I J a 1 n
      (by simpa only [Nat.add_comm 1 n] using hJ)
    simpa only [Nat.add_comm 1 n] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.HomogenizationTransform.Construction
