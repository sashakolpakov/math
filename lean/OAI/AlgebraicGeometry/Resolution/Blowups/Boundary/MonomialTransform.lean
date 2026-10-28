import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialExponentBound

/-! # Monomial Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialTransform.Construction

noncomputable section

/-! Every permissible controlled transform of a labelled boundary monomial is again a labelled monomial. -/

universe u v

theorem boundaryMonomialElement_mixed_totalIdeal
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (d : I) (F : Finset ι) (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I) (a : ι → ℕ) :
    (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}).map (Blowup.Charts.Construction.blowupChartConstants I d) =
      Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw)
        (fun j : Option ι => match j with | none => ∑ l ∈ F, a l | some l => a l)} := by
  rw [Ideal.map_span, Set.image_singleton]
  congr 1
  rw [LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement_mixed_factorization I d F w hw a,
    LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, Fintype.prod_option]
  rfl

theorem blowupControlledTransform_of_unit_exceptional
    {R : Type u} [CommRing R] (I M : Ideal R) (d : I) (b : ℕ)
    (hc : IsUnit (Blowup.Charts.Construction.blowupChartConstants I d d.val)) :
    ControlledTransform.Construction.blowupControlledTransform I M b d = M.map (Blowup.Charts.Construction.blowupChartConstants I d) := by
  ext x
  rw [ControlledTransform.Construction.blowupControlledTransform, Ideal.mem_colon_span_singleton,
    mul_comm x (Blowup.Charts.Construction.blowupChartConstants I d d.val ^ b)]
  exact (M.map (Blowup.Charts.Construction.blowupChartConstants I d)).unit_mul_mem_iff_mem (hc.pow b)

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem boundary_monomial_center_weight_or_unit_exceptional
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (d : I) (F : Finset ι) (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I)
    (a : ι → ℕ) (b : ℕ) (hM : Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} ≤ I ^ b)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I d)) (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw)) :
    b ≤ ∑ j ∈ F, a j ∨ IsUnit (Blowup.Charts.Construction.blowupChartConstants I d d.val) := by
  have h := ControlledTransform.Construction.blowup_totalTransform_le_exceptionalPower I (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}) b d hM
  rw [boundaryMonomialElement_mixed_totalIdeal I d F w hw a, ← Ideal.span_singleton_pow] at h
  exact hboundary.monomial_exponent_bound_or_unit
    (fun j : Option ι => match j with | none => ∑ l ∈ F, a l | some l => a l) none b h

theorem boundaryMonomialElement_controlledTransform_of_boundary
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (d : I) (F : Finset ι) (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I)
    (a : ι → ℕ) (b : ℕ) (hM : Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} ≤ I ^ b)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I d)) (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw)) :
    ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}) b d =
      Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw)
        (fun j : Option ι => match j with | none => (∑ l ∈ F, a l) - b | some l => a l)} := by
  by_cases hb : b ≤ ∑ j ∈ F, a j
  · exact LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement_controlledTransform I d F w hw a b hb
  · have hu := (boundary_monomial_center_weight_or_unit_exceptional R I d F w hw a b hM hboundary).resolve_left hb
    let c := Blowup.Charts.Construction.blowupChartConstants I d d.val
    let q := ∏ j, MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw (some j) ^ a j
    have hnext : LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw)
        (fun j : Option ι => match j with | none => (∑ l ∈ F, a l) - b | some l => a l) =
        c ^ ((∑ l ∈ F, a l) - b) * q := by
      rw [LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, Fintype.prod_option]
      rfl
    rw [blowupControlledTransform_of_unit_exceptional I _ d b hu, Ideal.map_span,
      Set.image_singleton, LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement_mixed_factorization I d F w hw a, hnext,
      Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hb)), pow_zero c, one_mul q]
    exact Ideal.span_singleton_mul_left_unit (hu.pow (∑ j ∈ F, a j)) q

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialTransform.Construction
