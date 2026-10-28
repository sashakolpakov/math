import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingReferenceHermitian
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

/-! # Field Marking Reference Embedding -/

namespace OAI.RepresentationTheory.Theta.Geometric.FieldMarkingReferenceEmbedding

noncomputable section

/-! The actual marked reference Hermitian equality holds in every
complex embedding block with the original diagonal normalization. -/

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

theorem fieldMarking_referenceEmbeddingHermitian
    (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hp : ∀ v w, PolarizedCanonicalForm.familyPolarizationForm A x (m v) (m w) = P.traceForm v w)
    (τ : E →ₐ[ℚ] ℂ) (v w : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian τ.toRingHom
      (Family.HermitianTransport.familyHermitianMatrix A ρ hρ x s hs hg hdegree (Reference.DiagonalHermitian.referenceTraceScalar P))
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m) τ v)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m) τ w) =
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian τ.toRingHom (Matrix.diagonal ![1, 1, P.b]) v w := by
  have he := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding.hermitianIsometry_embedding (Matrix.diagonal ![1, 1, P.b])
    (Family.HermitianTransport.familyHermitianMatrix A ρ hρ x s hs hg hdegree (Reference.DiagonalHermitian.referenceTraceScalar P))
    (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m).toLinearMap
    (FieldMarkingReferenceHermitian.fieldMarking_referenceHermitian A ρ x s hs hg hdegree m hρ P hP hp) τ v w
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply] at he
  have hτ (t : E) : τ.toRingHom t = τ t := rfl
  simpa only [AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso_apply, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian, Matrix.map_apply, hτ] using he

end

end OAI.RepresentationTheory.Theta.Geometric.FieldMarkingReferenceEmbedding
