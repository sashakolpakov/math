import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPolarization
import OAI.RepresentationTheory.Theta.Geometric.Family.HermitianTransport
import OAI.RepresentationTheory.Theta.Geometric.Reference.DiagonalHermitian

/-! # Field Marking Reference Hermitian -/

namespace OAI.RepresentationTheory.Theta.Geometric.FieldMarkingReferenceHermitian

noncomputable section

/-! A field marking with the original trace polarization identifies
the reconstructed fiber Hermitian form with the exact reference diagonal. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (m : let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety)

theorem fieldMarking_referenceHermitian
    (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hp : ∀ v w, PolarizedCanonicalForm.familyPolarizationForm A x (m v) (m w) = P.traceForm v w)
    (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian
      (Family.HermitianTransport.familyHermitianMatrix A ρ hρ x s hs hg hdegree (Reference.DiagonalHermitian.referenceTraceScalar P))
      (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m v)
      (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m w) =
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian (Matrix.diagonal ![1, 1, P.b]) v w := by
  rw [Reference.DiagonalHermitian.matrixHermitian_reference_diagonal]
  apply Reference.DiagonalHermitian.reference_trace_reconstruction (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm_rosati (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree (hρ.pullback A ρ x.left))
    (Reference.DiagonalHermitian.referenceTraceScalar P) P.b (Reference.DiagonalHermitian.referenceTraceScalar_ne_zero P hP)
    (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m)
  intro u t
  rw [← Family.MarkedPolarization.familyMarkedPolarizationForm_original, FieldMarkingPolarization.fieldMarkingCoordinates_polarization, hp,
    Reference.DiagonalHermitian.referenceTraceScalar_formula]

end

end OAI.RepresentationTheory.Theta.Geometric.FieldMarkingReferenceHermitian
