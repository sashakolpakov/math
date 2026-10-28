import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceIsometries
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization

/-! # Marked Polarization Isometry -/

namespace OAI.RepresentationTheory.Theta.Geometric.MarkedPolarizationIsometry

noncomputable section

/-! Original rational polarization isometries give exact isometries of
the reconstructed Hermitian matrices, by the nondegenerate field trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceIsometries.TraceReconstruction

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hσ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation B σ)
    (ξ : E) (hξ : ξ ≠ 0) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

include hξ in
theorem markedPolarization_isometry_hermitian
    (hu : ∀ x y, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm B σ s hs hg hdegree (u x) (u y) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree x y)
    (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B σ s hs hg hdegree hσ ξ) (u x) (u y) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y := by
  have h := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceIsometries.TraceReconstruction.hermitianCoefficient_isometry_iff ξ hξ
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm B σ s hs hg hdegree)
    u.toLinearMap).mpr hu x y
  exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction.hermitianMatrix_evaluate ξ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm B σ s hs hg hdegree)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm_rosati B σ s hs hg hdegree hσ) (u x) (u y)).trans
      (h.trans (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction.hermitianMatrix_evaluate ξ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree)
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm_rosati A ρ s hs hg hdegree hρ) x y).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.MarkedPolarizationIsometry
