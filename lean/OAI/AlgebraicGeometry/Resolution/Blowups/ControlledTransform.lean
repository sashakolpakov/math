import OAI.AlgebraicGeometry.Resolution.Blowups.ExceptionalIdeal
import Mathlib.RingTheory.Ideal.Colon

/-! # Controlled Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransform.Construction

noncomputable section

/-! Controlled transforms of ideals on the actual affine blowup charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R]

/-- An ideal contained in a principal ideal factors through its ideal quotient. -/
theorem principal_mul_colon_of_le (J : Ideal R) (c : R) (hJ : J ≤ Ideal.span {c}) :
    Ideal.span {c} * J.colon (Ideal.span {c}) = J := by
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro x hx y hy
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hx
    have hyc := Ideal.mem_colon_span_singleton.mp hy
    convert J.mul_mem_left d hyc using 1
    ring
  · intro x hx
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hJ hx)
    rw [hd]
    apply Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton c))
    apply Ideal.mem_colon_span_singleton.mpr
    simpa only [mul_comm d c, ← hd] using hx

variable (I J : Ideal R) (b : ℕ) (a : I)

/-- The controlled transform divides the total transform by the specified
power of the exceptional parameter, using an actual ideal quotient. -/
def blowupControlledTransform : Ideal (Blowup.Charts.Construction.blowupChart I a) :=
  (J.map (Blowup.Charts.Construction.blowupChartConstants I a)).colon
    (Ideal.span {(Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ b})

/-- A center contained to order `b` gives total-transform divisibility by
the `b`th power of the exceptional parameter. -/
theorem blowup_totalTransform_le_exceptionalPower (hJI : J ≤ I ^ b) :
    J.map (Blowup.Charts.Construction.blowupChartConstants I a) ≤
      Ideal.span {(Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ b} := by
  calc
    J.map (Blowup.Charts.Construction.blowupChartConstants I a) ≤ (I ^ b).map (Blowup.Charts.Construction.blowupChartConstants I a) :=
      Ideal.map_mono hJI
    _ = Ideal.span {(Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ b} := by
      rw [Ideal.map_pow, ExceptionalIdeal.Construction.blowupChart_extendedIdeal, Ideal.span_singleton_pow]

/-- The total transform factors exactly into the exceptional power and
the controlled transform. -/
theorem blowup_controlledTransform_factorization (hJI : J ≤ I ^ b) :
    Ideal.span {(Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ b} * blowupControlledTransform I J b a =
      J.map (Blowup.Charts.Construction.blowupChartConstants I a) :=
  principal_mul_colon_of_le _ _ (blowup_totalTransform_le_exceptionalPower I J b a hJI)

/-- Division by the exceptional power is unique for every original section
whose order along the center is at least the control exponent. -/
theorem blowup_controlledTransform_unique_division (hJI : J ≤ I ^ b) (r : J) :
    ∃! q : Blowup.Charts.Construction.blowupChart I a,
      (Blowup.Charts.Construction.blowupChartConstants I a a.val) ^ b * q = Blowup.Charts.Construction.blowupChartConstants I a r.val := by
  have hr : Blowup.Charts.Construction.blowupChartConstants I a r.val ∈ J.map (Blowup.Charts.Construction.blowupChartConstants I a) :=
    Ideal.mem_map_of_mem _ r.property
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp
    (blowup_totalTransform_le_exceptionalPower I J b a hJI hr)
  refine ⟨q, hq.symm, ?_⟩
  intro q' hq'
  exact ((ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).pow b).left (hq'.trans hq)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransform.Construction
