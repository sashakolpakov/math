import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FiberHermitian
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HodgeLine

/-! # Fiber Ball Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Every actual complex PEL fiber supplies a normalized Hodge line
and hence a unique point in the literal ball domain of the datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))}

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.mem_domain_iff_diagonal (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    z ∈ P.domain ↔
      (Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0 := by
  change (Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b])
    (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0 ↔ _
  rw [Normalized.HodgeLine.complexMatrixHermitian_diagonal]

variable (A : PEL.Objects.PELObject P iota N T) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (p : Spec (.of ℂ) ⟶ T.left)

def PEL.Objects.PELObject.complexFiberHodgeLine (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) :
    Submodule ℂ (Fin 3 → ℂ) :=
  Normalized.HodgeLine.NativeHermitianMarking.nativeNormalizedHodgeLine (A.polarized.pullback p) (A.action.pullback p) s hs rfl hdegree
    (P.embeddings P.distinguished) e

variable [IsGalois ℚ E] (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom κ))

include hκ hp in
theorem PEL.Objects.PELObject.exists_complexFiber_ball_point (hP : P.IsAdmissible) :
    ∃ e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ),
      (∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ (A.complexFiberHermitianMatrix hs hdegree p) (e x) (e y) =
        Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y) ∧
      ∃! z : P.Domain, A.complexFiberHodgeLine hs hdegree p e = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z.val} := by
  obtain ⟨e, he⟩ := A.complexFiberHermitianMatrix_normalizer hs hdegree p κ hκ hp hP
  obtain ⟨hξ, hc, hi⟩ := Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP
  obtain ⟨z, ⟨hzline, hznegative⟩, hzunique⟩ := Normalized.HodgeLine.NativeHermitianMarking.exists_unique_nativeHodge_ball_coordinate
    (A.polarized.pullback p) (A.action.pullback p) s hs rfl hdegree (P.embeddings P.distinguished) e
    (ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati p) P.normalizedImaginaryScalar
    hξ hc hi P.b he (A.complexFiber_distinguished_rank κ hκ p hp hP)
  refine ⟨e, he, ⟨z, (Datum.RankThreePELDatum.mem_domain_iff_diagonal z).mpr hznegative⟩, hzline, ?_⟩
  intro w hw
  apply Subtype.ext
  exact hzunique w.val ⟨hw, (Datum.RankThreePELDatum.mem_domain_iff_diagonal w.val).mp w.property⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
