import OAI.RepresentationTheory.Theta.Geometric.Family.CentralNormalizer
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum

/-! # Ball Signs -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.BallSigns

noncomputable section

/-! The prescribed reference imaginary coefficient and literal ball
inequality in the diagonal coordinates used by the actual family periods. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def referencePositiveImaginaryScalar : E :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.ImaginaryHermitianWeights.positiveImaginaryScalar (P.embeddings P.distinguished) P.imaginaryScalar

theorem referencePositiveImaginaryScalar_spec (hP : P.IsAdmissible) :
    referencePositiveImaginaryScalar P ≠ 0 ∧
      AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (referencePositiveImaginaryScalar P) = -referencePositiveImaginaryScalar P ∧
      0 < (P.μ (referencePositiveImaginaryScalar P)).im :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.ImaginaryHermitianWeights.positiveImaginaryScalar_spec (P.embeddings P.distinguished) P.imaginaryScalar
    hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1

omit [NumberField.IsCMField E] in
theorem reference_ball_diagonal (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    z ∈ P.domain ↔
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0 := by
  change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b])
    (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0 ↔ _
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine.complexMatrixHermitian_diagonal]

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.BallSigns
