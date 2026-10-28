import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.DegreeIdealRelations

/-! # Generation Ideal Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-! The finite open generation conditions are equivalent to generation of the actual homogeneous ideal in the specified degree. -/

universe u v

variable {R : Type u} [CommRing R] {σ : Type v} {B : ℕ} {r : ℕ → ℕ}
variable (D : GradedClassification.TruncatedGradedQuotientData R σ B r) (N : ℕ) (hN : N ≤ B)

theorem GradedClassification.TruncatedGradedQuotientData.generatedFromDegree_iff_ideal_span : D.GeneratedFromDegree N ↔
    D.generatedIdeal.toIdeal = Ideal.span
      (((D.quotient ⟨N, Nat.lt_succ_of_le hN⟩).toSubmodule).map
        (MvPolynomial.homogeneousSubmodule σ R N).subtype : Set (MvPolynomial σ R)) := by
  constructor
  · exact D.generatedIdeal_span_degree N hN
  · intro hI
    constructor
    · intro d hd
      rw [← D.generatedIdeal_degree d]
      exact Single.DegreeIdealRelations.singleDegreeIdeal_relations_below N _ D.generatedIdeal hI d hd
    · intro d hd
      have h := Single.DegreeIdealRelations.singleDegreeIdeal_relations_succ N _ D.generatedIdeal hI d hd
      have ht := D.generatedIdeal_degree d.succ
      have hs := D.generatedIdeal_degree d.castSucc
      simp only [Fin.val_succ, Fin.val_castSucc] at ht hs
      rw [ht, hs] at h
      exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
