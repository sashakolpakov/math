import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodCoordinates

/-! # Intrinsic Coefficient Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientCoordinates

noncomputable section

/-! The original rank-three E-marking, restricted to rational scalars,
has exactly the coefficient coordinates used by CMPoints. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

omit [NumberField.IsCMField E] in
def nativeRationalCoefficientCoordinates :
    AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)) ≃ₗ[ℚ] (Fin 3 → E) := by
  let PA := AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := AbelianModuli.ReferenceFamily.Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldScalarTower A.abelian PA ρ
  exact (AbelianModuli.ReferenceFamily.Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree).restrictScalars ℚ

theorem nativeCoefficientCoordinates_pair
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (u : ComplexMultiplication.WeightOne.CM.Complexification (AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A)))) :
    PeriodCoordinates.cmPeriodCoordinates P hP
      ((nativeRationalCoefficientCoordinates A ρ s hs hg hdegree).toLinearMap.baseChange ℂ u) =
      (fun i => (AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u (P.embeddings i),
        AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingChernMatrix.IntrinsicHermitianMarking.nativeMarkedComplexCoordinates A ρ s hs hg hdegree u (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)))) := by
  funext i
  exact Prod.ext rfl rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientCoordinates
