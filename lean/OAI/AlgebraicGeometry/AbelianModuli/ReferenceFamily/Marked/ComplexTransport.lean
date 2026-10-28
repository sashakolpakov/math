import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns

/-! # Complex Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.ComplexTransport.IntrinsicHermitianMarking

noncomputable section

/-! The actual change of native rational marking acts on complex
embedding coordinates by its embedded matrix and preserves each
embedding eigenspace. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

def markedComplexTransport :=
  (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
    (Polarized.Projectivity.polarizedNativeProjectivePresentation B) ρ σ s hs hg hdegree u).toLinearMap.baseChange ℂ

omit [NumberField.IsCMField E] in
theorem markedComplexTransport_coordinates
    (v : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))))
    (τ : E →ₐ[ℚ] ℂ) :
    Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates B σ s hs hg hdegree (markedComplexTransport A B ρ σ s hs hg hdegree u v) τ =
      ((LinearMap.toMatrix' u.toLinearMap).map τ).mulVec
        (Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree v τ) := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let PB := Polarized.Projectivity.polarizedNativeProjectivePresentation B
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian PB σ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.abelian PB σ
  exact EmbeddingMatrixTransport.rankThreeComplexCoordinates_map (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree)
    (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B.abelian PB σ s hs hg hdegree)
    (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian PA PB ρ σ s hs hg hdegree u).toLinearMap
    u.toLinearMap (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates A.abelian B.abelian PA PB ρ σ s hs hg hdegree u) v τ

omit [NumberField.IsCMField E] in
theorem markedComplexTransport_embedding
    (τ : E →ₐ[ℚ] ℂ)
    (v : ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))))
    (hv : v ∈ EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A) ρ τ) :
    markedComplexTransport A B ρ σ s hs hg hdegree u v ∈
      EmbeddingPeriodProjection.IntrinsicNumberFieldAction.nativeEmbeddingSpace B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation B) σ τ := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let PB := Polarized.Projectivity.polarizedNativeProjectivePresentation B
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian PB σ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower B.abelian PB σ
  apply (RankThreeEmbeddingCoordinates.rankThreeEmbedding_mem_iff E (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B.abelian PB σ s hs hg hdegree) τ _).mpr
  intro κ hκ
  have hz := (RankThreeEmbeddingCoordinates.rankThreeEmbedding_mem_iff E (Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree) τ v).mp hv κ hκ
  have ht := markedComplexTransport_coordinates A B ρ σ s hs hg hdegree u v κ
  exact ht.trans ((congrArg (((LinearMap.toMatrix' u.toLinearMap).map κ).mulVec) hz).trans (Matrix.mulVec_zero _))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.ComplexTransport.IntrinsicHermitianMarking
