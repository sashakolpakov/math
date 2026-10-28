import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicEmbeddingPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement

/-! # Intrinsic Line Annihilator -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLineAnnihilator

noncomputable section

/-! When the actual distinguished Hodge summand is a line, the
conjugate summand is exactly its bilinear annihilator for the original
polarization. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem native_conjugate_part_iff_line_annihilator
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (τ : E →ₐ[ℚ] ℂ) (v w : Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hline : AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ = Submodule.span ℂ {v}) :
    w ∈ AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) ↔
      Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => τ) (AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) () v w = 0 := by
  constructor
  · intro hw
    apply IntrinsicEmbeddingPeriods.native_conjugate_period_part_orthogonal A ρ s hs hg hdegree hρ ξ hξ τ v w
    · rw [hline]
      exact Submodule.mem_span_singleton_self v
    · exact hw
  · intro hw
    apply (AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking.nativePositivePart_conjugate_iff A ρ s hs hg hdegree τ w).mpr
    let F := AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement.IntrinsicHermitianMarking.weightedEmbeddingForm A ρ s hs hg hdegree hρ ξ τ
    apply AbelianModuli.ReferenceFamily.Hermitian.Complement.mem_complement_of_orthogonal F
      (AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ)
      (AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree τ)
      (AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_isCompl A ρ s hs hg hdegree τ)
    · intro x hx hn
      rw [AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement.IntrinsicHermitianMarking.weightedEmbeddingForm_apply]
      exact AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_positive A ρ s hs hg hdegree τ hρ ξ hξ x hx hn
    · intro x hx y hy
      rw [AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement.IntrinsicHermitianMarking.weightedEmbeddingForm_apply]
      exact AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_orthogonal A ρ s hs hg hdegree τ hρ ξ hξ x y hx hy
    · intro x hx
      have hv : F v (star w) = 0 := by
        rw [AbelianModuli.ReferenceFamily.Intrinsic.HermitianComplement.IntrinsicHermitianMarking.weightedEmbeddingForm_apply]
        change (Complex.I * τ ξ) * AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian τ.toRingHom
          (AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) v (star w) = 0
        have he : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian τ.toRingHom
            (AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) v (star w) = 0 := by
          simpa [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian, Geometry.ComplexBall.PrescribedSignsB.localB] using hw
        rw [he, mul_zero]
      rw [hline] at hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp only [map_smul, LinearMap.smul_apply, hv, smul_zero]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLineAnnihilator
