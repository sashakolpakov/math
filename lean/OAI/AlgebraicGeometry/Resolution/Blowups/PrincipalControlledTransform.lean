import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Principal Controlled Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalControlledTransform.Construction

noncomputable section

/-! Exact principal generators of controlled transforms on actual Rees charts. -/

universe u

theorem exists_principal_controlled_transform_generator
    {R : Type u} [CommRing R] (I : Ideal R) (z : R) (b : ℕ) (a : I)
    (hp : Ideal.span {z} ≤ I ^ b) :
    ∃ q : Blowup.Charts.Construction.blowupChart I a, ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {z}) b a = Ideal.span {q} := by
  obtain ⟨q, hq, _⟩ := ControlledTransform.Construction.blowup_controlledTransform_unique_division I (Ideal.span {z}) b a hp
    ⟨z, Ideal.mem_span_singleton_self z⟩
  have hc : IsRegular (Blowup.Charts.Construction.blowupChartConstants I a a.val ^ b) :=
    IsRegular.pow (a := Blowup.Charts.Construction.blowupChartConstants I a a.val) b (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
  refine ⟨q, ?_⟩
  unfold ControlledTransform.Construction.blowupControlledTransform
  rw [Ideal.map_span, Set.image_singleton, ← hq,
    ← Ideal.span_singleton_mul_span_singleton]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular (Ideal.span {q}) (Blowup.Charts.Construction.blowupChartConstants I a a.val ^ b) hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalControlledTransform.Construction
