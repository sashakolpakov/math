import OAI.AlgebraicGeometry.PELModuli.CMPoints.EmbeddingHodgeMembership
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation

/-! # Intrinsic Embedding Periods -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicEmbeddingPeriods

noncomputable section

/-! The actual period kernel is exactly the collection of its native
embedding Hodge parts. The original polarization gives the precise
bilinear annihilator condition at conjugate embeddings. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

omit [NumberField.IsCMField E] in
theorem nativePeriodKernel_iff_embedding_coordinates
    (u : ComplexMultiplication.WeightOne.CM.Complexification (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)))) :
    u ∈ (AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))).ker ↔
      ∀ τ : E →ₐ[ℚ] ℂ,
        AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u τ ∈
          AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ := by
  let PA := AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  exact EmbeddingHodgeMembership.holomorphic_iff_embedding_coordinates E (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree)
    (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian PA))
    (fun a => AbelianModuli.ReferenceFamily.Complex.PeriodFieldAction.IntrinsicNumberFieldAction.fieldAction_isHodgeMap A.abelian PA ρ a) u

theorem native_conjugate_period_part_orthogonal
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (τ : E →ₐ[ℚ] ℂ) (v w : Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hv : v ∈ AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ)
    (hw : w ∈ AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)) :
    Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => τ) (AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) () v w = 0 := by
  have hwn := (AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking.nativePositivePart_conjugate_iff A ρ s hs hg hdegree τ w).mp hw
  have h := AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_orthogonal A ρ s hs hg hdegree τ hρ ξ hξ v (star w) hv hwn
  have hn : Complex.I * τ ξ ≠ 0 := mul_ne_zero Complex.I_ne_zero ((map_ne_zero τ).mpr hξ)
  change (Complex.I * τ ξ) * AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian τ.toRingHom
    (AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) v (star w) = 0 at h
  have hz := (mul_eq_zero.mp h).resolve_left hn
  simpa [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian, Geometry.ComplexBall.PrescribedSignsB.localB] using hz

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicEmbeddingPeriods
