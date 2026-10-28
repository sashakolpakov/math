import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FiberBallPoint

/-! # Pointwise Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.PointwiseComparison

noncomputable section

/-! Every actual PEL fiber satisfies the coefficient Hodge equations
for any chosen normalizer of its actual Hermitian matrix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_PEL_fiber_coefficient_comparison
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] {s N : ℕ}
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (hP : P.IsAdmissible)
    {iota : E →+* K} {T : Over (Spec (.of K))}
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (p : Spec (.of ℂ) ⟶ T.left) (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom κ))
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ
      (A.complexFiberHermitianMatrix hs hdegree p) (e x) (e y) =
        AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y) :
    ∃ z : P.Domain, ∀ x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E),
      x ∈ (IntrinsicCoefficientRealization.nativeCoefficientHodgeStructure (A.polarized.pullback p) (A.action.pullback p)
        s hs rfl hdegree).holomorphic ↔
      ClosedCoefficientPeriods.componentPrescribed P (A.complexFiberHermitianMatrix hs hdegree p)
        (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (PeriodCoordinates.cmPeriodCoordinates P hP x) := by
  obtain ⟨hξ, hc, hi⟩ := AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP
  obtain ⟨z, ⟨hzline, hznegative⟩, _⟩ := AbelianModuli.ReferenceFamily.Normalized.HodgeLine.NativeHermitianMarking.exists_unique_nativeHodge_ball_coordinate
    (A.polarized.pullback p) (A.action.pullback p) s hs rfl hdegree (P.embeddings P.distinguished) e
    (AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati p) P.normalizedImaginaryScalar
    hξ hc hi P.b he (A.complexFiber_distinguished_rank κ hκ p hp hP)
  refine ⟨⟨z, (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.mem_domain_iff_diagonal z).mpr hznegative⟩, ?_⟩
  intro x
  exact IntrinsicCoefficientComparison.nativeCoefficientHodgeStructure_holomorphic P hP
    (A.polarized.pullback p) (A.action.pullback p) hs rfl hdegree
    (AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati p) P.normalizedImaginaryScalar hξ
    e z hzline (A.complexFiber_embedding_rank κ hκ p hp hP) x

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.PointwiseComparison
