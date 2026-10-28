import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models

/-! # Paired Embedding Labels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedEmbeddingLabels.Construction

/-! Relabel the same conjugate block indices for the two-sided pairing
formula, retaining the original labels and their conjugation rule. -/

def pairedIndexEquiv (s : ℕ) : (Fin s ⊕ Fin s) ≃ (Fin s × Bool) where
  toFun
    | Sum.inl i => (i, false)
    | Sum.inr i => (i, true)
  invFun
    | (i, false) => Sum.inl i
    | (i, true) => Sum.inr i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, b⟩; cases b <;> rfl

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hc : ∀ i, labels (i, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (i, false))

def pairedEmbeddingLabels : (Fin s ⊕ Fin s) ≃ Gal(E/ℚ) :=
  (pairedIndexEquiv s).trans labels

include hc in
theorem pairedEmbeddingLabels_conjugate (i : Fin s ⊕ Fin s) :
    pairedEmbeddingLabels s labels (Sum.swap i) =
      PELModuli.CMPoints.Arithmetic.rationalConjugation E * pairedEmbeddingLabels s labels i := by
  cases i with
  | inl v => exact hc v
  | inr v =>
      change labels (v, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, true)
      rw [hc, ← mul_assoc, PELModuli.CMPoints.Models.rationalConjugation_mul_self, one_mul]

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedEmbeddingLabels.Construction
