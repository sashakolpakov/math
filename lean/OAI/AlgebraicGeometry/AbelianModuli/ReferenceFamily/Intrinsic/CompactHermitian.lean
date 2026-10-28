import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ImaginaryHermitianWeights

/-! # Compact Hermitian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CompactHermitian.IntrinsicHermitianMarking

noncomputable section

/-! Extreme actual Lie ranks force definite Hermitian blocks at the
compact embeddings. The sign of the imaginary trace weight is retained
and then removed by a real sign calculation. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (σ : E →ₐ[ℚ] ℂ) (hρ : ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)

include hξ in
theorem weightedEmbeddingHermitian_definite {r : ℕ}
    (hr : LieRanks.HasLieRank A.abelian ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r)
    (hextreme : r = 0 ∨ r = 3) :
    (∀ x : Fin 3 → ℂ, x ≠ 0 → 0 < (EmbeddingSigns.IntrinsicHermitianMarking.weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ x x).re) ∨
    (∀ x : Fin 3 → ℂ, x ≠ 0 → (EmbeddingSigns.IntrinsicHermitianMarking.weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ x x).re < 0) := by
  rcases hextreme with rfl | rfl
  · have hd : Module.finrank ℂ (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree σ) = 3 :=
      EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_finrank A ρ s hs hg hdegree σ hr
    have ht : EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree σ = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hd.trans (Module.finrank_fin_fun ℂ).symm)
    left
    intro x hx
    apply EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_positive A ρ s hs hg hdegree σ hρ ξ hξ x _ hx
    rw [ht]
    trivial
  · have hd : Module.finrank ℂ (EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree σ) = 3 :=
      EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart_finrank A ρ s hs hg hdegree σ hr
    have ht : EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree σ = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hd.trans (Module.finrank_fin_fun ℂ).symm)
    right
    intro x hx
    apply EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart_negative A ρ s hs hg hdegree σ hρ ξ hξ x _ hx
    rw [ht]
    trivial

include hξ in
theorem nativeHermitianMatrix_definite_of_LieRank {r : ℕ}
    (hconj : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ)
    (hr : LieRanks.HasLieRank A.abelian ρ (σ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r)
    (hextreme : r = 0 ∨ r = 3) :
    (∀ x : Fin 3 → ℂ, x ≠ 0 → 0 < (Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom
      (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x x).re) ∨
    (∀ x : Fin 3 → ℂ, x ≠ 0 → (Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom
      (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x x).re < 0) := by
  let B : (Fin 3 → ℂ) → ℝ := fun x => (Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom
    (HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x x).re
  have hc : -(σ ξ).im ≠ 0 := neg_ne_zero.mpr (ImaginaryHermitianWeights.imaginaryScalar_embedding_im_ne_zero σ ξ hξ hconj)
  have hw (x : Fin 3 → ℂ) :
      (EmbeddingSigns.IntrinsicHermitianMarking.weightedEmbeddingHermitian A ρ s hs hg hdegree hρ ξ σ x x).re = -(σ ξ).im * B x :=
    ImaginaryHermitianWeights.imaginaryHermitianWeight_re (σ ξ) _ (ImaginaryHermitianWeights.imaginaryScalar_embedding_re σ ξ hconj)
  apply ImaginaryHermitianWeights.definite_of_real_weight B (-(σ ξ).im) hc
  rcases weightedEmbeddingHermitian_definite A ρ s hs hg hdegree σ hρ ξ hξ hr hextreme with h | h
  · left
    intro x hx
    exact hw x ▸ h x hx
  · right
    intro x hx
    exact hw x ▸ h x hx

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CompactHermitian.IntrinsicHermitianMarking
