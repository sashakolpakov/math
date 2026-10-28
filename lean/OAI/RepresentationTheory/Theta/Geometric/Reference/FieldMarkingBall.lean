import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingReferenceEmbedding
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank
import OAI.RepresentationTheory.Theta.Geometric.Reference.BallSigns

/-! # Field Marking Ball -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.FieldMarkingBall

noncomputable section

section

/-! One actual reference kernel and its original polarization force
the distinguished imaginary trace coefficient to have the reference sign. -/

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

include hs hg hdegree in
theorem fieldMarking_referenceImaginary_positive
    (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hp : ∀ v w, PolarizedCanonicalForm.familyPolarizationForm A x (m v) (m w) = P.traceForm v w)
    (a : P.domain)
    (hk : (FieldMarkingKernelRank.fieldMarkingFirstProjection A ρ x s m P hP).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector a.val}) :
    0 < ((P.embeddings P.distinguished) (DiagonalHermitian.referenceTraceScalar P)).im := by
  let τ := P.embeddings P.distinguished
  let ξ := DiagonalHermitian.referenceTraceScalar P
  let e := AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m) τ
  let v := Geometry.ComplexBall.PrescribedSignsB.lineVector a.val
  have hmem : e v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree τ := by
    have hv : v ∈ (FieldMarkingKernelRank.fieldMarkingFirstProjection A ρ x s m P hP).ker :=
      hk.symm ▸ Submodule.mem_span_singleton_self v
    rw [FieldMarkingKernelRank.fieldMarkingFirstProjection_kernel A ρ x s hs hg hdegree m P hP] at hv
    exact hv
  have hne : e v ≠ 0 := fun hz => Geometry.ComplexBall.PrescribedSignsB.lineVector_ne_zero a.val (e.injective (hz.trans e.map_zero.symm))
  have hw := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_positive (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree τ
    (hρ.pullback A ρ x.left) ξ (DiagonalHermitian.referenceTraceScalar_ne_zero P hP) (e v) hmem hne
  have hweight := AlgebraicGeometry.AbelianModuli.ReferenceFamily.ImaginaryHermitianWeights.imaginaryHermitianWeight_re (τ ξ)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian τ.toRingHom
      (Family.HermitianTransport.familyHermitianMatrix A ρ hρ x s hs hg hdegree ξ) (e v) (e v))
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ImaginaryHermitianWeights.imaginaryScalar_embedding_re τ ξ (DiagonalHermitian.referenceTraceScalar_conjugate P hP))
  have hw' := (congrArg (fun r : ℝ => 0 < r) hweight).mp hw
  have he := FieldMarkingReferenceEmbedding.fieldMarking_referenceEmbeddingHermitian A ρ x s hs hg hdegree m hρ P hP hp τ v v
  rw [he, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine.complexMatrixHermitian_diagonal] at hw'
  have hn := (BallSigns.reference_ball_diagonal P a.val).mp a.property
  change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, τ P.b]) v v).re < 0 at hn
  have ht : τ.toRingHom P.b = τ P.b := rfl
  rw [ht] at hw'
  change 0 < (τ ξ).im
  nlinarith

end

/-! Every actual rank-two fiber with the original marked trace form
has a distinguished kernel in the literal reference ball. -/

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

include hs hg hdegree in
theorem fieldMarking_referenceBallCoordinate
    (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hp : ∀ v w, PolarizedCanonicalForm.familyPolarizationForm A x (m v) (m w) = P.traceForm v w)
    (him : 0 < ((P.embeddings P.distinguished) (DiagonalHermitian.referenceTraceScalar P)).im)
    (hr : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback x.left) (ρ.pullback x.left)
      ((P.embeddings P.distinguished).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2) :
    ∃ w : P.domain, (FieldMarkingKernelRank.fieldMarkingFirstProjection A ρ x s m P hP).ker =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w.val} := by
  let τ := P.embeddings P.distinguished
  let ξ := DiagonalHermitian.referenceTraceScalar P
  let e := AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m) τ
  obtain ⟨w, ⟨hk, hn⟩, _⟩ := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine.NativeHermitianMarking.exists_unique_nativeHodge_ball_coordinate
    (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree τ e
    (hρ.pullback A ρ x.left) ξ (DiagonalHermitian.referenceTraceScalar_ne_zero P hP)
    (DiagonalHermitian.referenceTraceScalar_conjugate P hP) him P.b
    (FieldMarkingReferenceEmbedding.fieldMarking_referenceEmbeddingHermitian A ρ x s hs hg hdegree m hρ P hP hp τ) hr
  refine ⟨⟨w, (BallSigns.reference_ball_diagonal P w).mpr hn⟩, ?_⟩
  rw [FieldMarkingKernelRank.fieldMarkingFirstProjection_kernel A ρ x s hs hg hdegree m P hP,
    Submodule.comap_equiv_eq_map_symm]
  exact hk

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.FieldMarkingBall
