import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationIdealCriterion

/-! # Degree Determination -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Generated finite quotient data are determined by their quotient in the generating degree, over any coefficient ring. -/

universe u v

variable {R : Type u} [CommRing R] {σ : Type v} {B N : ℕ} {r : ℕ → ℕ}
variable (D E : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r) (hN : N ≤ B)
variable (hD : D.GeneratedFromDegree N) (hE : E.GeneratedFromDegree N)

include hD hE in
theorem Truncated.GradedClassification.TruncatedGradedQuotientData.generatedIdeal_eq_of_generating_quotient_eq
    (h : D.quotient ⟨N, Nat.lt_succ_of_le hN⟩ = E.quotient ⟨N, Nat.lt_succ_of_le hN⟩) :
    D.generatedIdeal = E.generatedIdeal := by
  apply HomogeneousIdeal.ext
  rw [D.generatedIdeal_span_degree N hN hD, E.generatedIdeal_span_degree N hN hE, h]

include hD hE in
theorem Truncated.GradedClassification.TruncatedGradedQuotientData.eq_of_generating_quotient_eq
    (h : D.quotient ⟨N, Nat.lt_succ_of_le hN⟩ = E.quotient ⟨N, Nat.lt_succ_of_le hN⟩) : D = E := by
  have hi := D.generatedIdeal_eq_of_generating_quotient_eq E hN hD hE h
  apply Truncated.GradedClassification.TruncatedGradedQuotientData.ext
  funext d
  apply Module.Grassmannian.ext
  rw [← D.generatedIdeal_degree d, ← E.generatedIdeal_degree d, hi]

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.generatingQuotient_injective : Function.Injective
    (fun D : {D : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r // D.GeneratedFromDegree N} =>
      D.val.quotient ⟨N, Nat.lt_succ_of_le hN⟩) := by
  intro D E h
  exact Subtype.ext (D.val.eq_of_generating_quotient_eq E.val hN D.property E.property h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
