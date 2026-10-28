import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns

/-! # Embedding Conjugation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking

noncomputable section

/-! Coefficient conjugation swaps the actual marked positive and
negative Hodge subspaces and conjugates the field embedding. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem nativeEmbedding_conjugation (τ : E →ₐ[ℚ] ℂ)
    (v : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))))
    (hv : v ∈ EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ τ) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation _ v ∈
      EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ
  exact ComplexMultiplication.EmbeddingHodgeType.CM.coefficientConjugation_mem_embeddingSpace E _ τ hv

theorem nativeMarkedCoordinates_conjugation
    (v : ComplexMultiplication.WeightOne.CM.Complexification (RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))))
    (τ : E →ₐ[ℚ] ℂ) :
    EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree (ComplexMultiplication.WeightOne.CM.coefficientConjugation _ v) τ =
      star (EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree v (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)) := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  funext i
  exact EmbeddingTracePairing.rankThreeComplexCoordinates_conjugation (PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree) v τ i

theorem nativePositivePart_conjugation (τ : E →ₐ[ℚ] ℂ) (x : Fin 3 → ℂ)
    (hx : x ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ) :
    star x ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) := by
  obtain ⟨v, hv, rfl⟩ := hx
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let w : EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian PA ρ (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) :=
    ⟨ComplexMultiplication.WeightOne.CM.coefficientConjugation _ v.val, nativeEmbedding_conjugation A ρ τ v.val v.property⟩
  have hw : w.val ∈ IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.conjugatePeriodKernel (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA) :=
    ((IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA)).conjugate_mem v.val).mpr hv
  refine ⟨w, hw, ?_⟩
  have h := nativeMarkedCoordinates_conjugation A ρ s hs hg hdegree v.val (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)
  rw [ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive] at h
  exact h

theorem nativeNegativePart_conjugation (τ : E →ₐ[ℚ] ℂ) (x : Fin 3 → ℂ)
    (hx : x ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree τ) :
    star x ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) := by
  obtain ⟨v, hv, rfl⟩ := hx
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let w : EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian PA ρ (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) :=
    ⟨ComplexMultiplication.WeightOne.CM.coefficientConjugation _ v.val, nativeEmbedding_conjugation A ρ τ v.val v.property⟩
  have hw : w.val ∈ (PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA)).ker := hv
  refine ⟨w, hw, ?_⟩
  have h := nativeMarkedCoordinates_conjugation A ρ s hs hg hdegree v.val (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)
  rw [ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive] at h
  exact h

theorem nativePositivePart_conjugate_iff (τ : E →ₐ[ℚ] ℂ) (x : Fin 3 → ℂ) :
    x ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) ↔
      star x ∈ EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree τ := by
  constructor
  · intro hx
    simpa only [ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive] using
      nativePositivePart_conjugation A ρ s hs hg hdegree (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) x hx
  · intro hx
    simpa only [star_star] using nativeNegativePart_conjugation A ρ s hs hg hdegree τ (star x) hx

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking
