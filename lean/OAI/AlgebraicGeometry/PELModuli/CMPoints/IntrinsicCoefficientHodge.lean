import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicLineAnnihilator
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ClosedCoefficientPeriods

/-! # Intrinsic Coefficient Hodge -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientHodge

noncomputable section

/-! The actual PEL Lie ranks and the native normalized Hodge line give
all clauses of the literal coefficient-period condition. -/

open scoped Classical

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking

theorem submodule_eq_span_of_normalized_line
    (S : Submodule ℂ Geometry.ComplexBall.PrescribedSignsB.Vec) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (h : S.map e.symm.toLinearMap = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}) :
    S = Submodule.span ℂ {e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)} := by
  apply (Submodule.orderIsoMapComap e.symm).injective
  change S.map e.symm.toLinearMap =
    (Submodule.span ℂ {e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)}).map e.symm.toLinearMap
  rw [h, Submodule.map_span, Set.image_singleton]
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem native_period_holomorphic_iff_component
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N s : ℕ} {δ : Fin g → ℕ}
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (ξ : E) (hξ : ξ ≠ 0)
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hline : AbelianModuli.ReferenceFamily.Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine A ρ s hs hg hdegree (P.embeddings P.distinguished) e =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z})
    (hrank : ∀ i : Fin s, AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i))
    (u : ComplexMultiplication.WeightOne.CM.Complexification (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)))) :
    u ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))).holomorphic ↔
      ClosedCoefficientPeriods.componentPrescribed P (AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z))
        (fun i => (AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u (P.embeddings i),
          AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)))) := by
  have hS : AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (P.embeddings P.distinguished) =
      Submodule.span ℂ {e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)} :=
    submodule_eq_span_of_normalized_line _ e z hline
  let c := AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u
  have hpart (i : Fin s) :
      (c (P.embeddings i) ∈ AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (P.embeddings i) ∧
        c (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) ∈
          AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i))) ↔
      (if i = P.distinguished then
        c (P.embeddings i) ∈ Submodule.span ℂ {e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)} ∧
          Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) i
            (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) (c (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i))) = 0
      else if P.compactSigns i then c (P.embeddings i) = 0
      else c (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)) = 0) := by
    by_cases hi : i = P.distinguished
    · subst i
      simp only [ite_true]
      exact and_congr (by rw [hS])
        (IntrinsicLineAnnihilator.native_conjugate_part_iff_line_annihilator A ρ s hs hg hdegree hρ ξ hξ
          (P.embeddings P.distinguished) (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z))
          (c (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings P.distinguished))) hS)
    · simp only [hi, ite_false]
      by_cases hsign : P.compactSigns i = true
      · have hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ
            ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 3 := by
          simpa only [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank, hi, ite_false, hsign, ite_true] using hrank i
        have hbot := AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking.nativePositivePart_eq_bot_of_rank_three A ρ s hs hg hdegree (P.embeddings i) hr
        have htop : AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree (P.embeddings i) = ⊤ :=
          eq_top_of_bot_isCompl (hbot ▸ AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_isCompl A ρ s hs hg hdegree (P.embeddings i))
        rw [hsign, ite_eq_left rfl, AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking.nativePositivePart_conjugate_iff, hbot, htop]
        simp
      · have hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ
            ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 0 := by
          simpa [AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank, hi, hsign] using hrank i
        have htop := AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking.nativePositivePart_eq_top_of_rank_zero A ρ s hs hg hdegree (P.embeddings i) hr
        have hbot : AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianNegativePart A ρ s hs hg hdegree (P.embeddings i) = ⊥ :=
          eq_bot_of_top_isCompl (htop ▸ AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianParts_isCompl A ρ s hs hg hdegree (P.embeddings i))
        rw [ite_eq_right hsign, AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingConjugation.IntrinsicHermitianMarking.nativePositivePart_conjugate_iff, htop, hbot]
        simp
  rw [show u ∈ (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))).holomorphic ↔
    ∀ τ, c τ ∈ AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ from
      IntrinsicEmbeddingPeriods.nativePeriodKernel_iff_embedding_coordinates A ρ s hs hg hdegree u]
  unfold ClosedCoefficientPeriods.componentPrescribed
  constructor
  · intro hu i
    exact (hpart i).mp ⟨hu (P.embeddings i), hu (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i))⟩
  · intro hu τ
    obtain ⟨⟨i, b⟩, rfl⟩ := (NumberTheory.ArithmeticGroups.EmbeddingLattice.CongruenceLevel.representativePairs P.embeddings hP.1).surjective τ
    cases b
    · exact ((hpart i).mpr (hu i)).1
    · exact ((hpart i).mpr (hu i)).2

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientHodge
