import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

/-! # Hermitian Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HermitianTransport

noncomputable section

/-! Hermitian normalizers conjugate an embedded E-isometry to an
isometry of the prescribed diagonal form. Its affine line formula
therefore has a nonzero denominator on the actual negative domain. -/

theorem normalizedHermitian_isometry
    (F G D : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) →ₗ⋆[ℂ] ℂ)
    (eA eB f : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (hA : ∀ x y, F (eA x) (eA y) = D x y)
    (hB : ∀ x y, G (eB x) (eB y) = D x y)
    (hf : ∀ x y, G (f x) (f y) = F x y) (x y : Fin 3 → ℂ) :
    D (NegativeLine.normalizedLineMap eA eB f x) (NegativeLine.normalizedLineMap eA eB f y) = D x y := by
  have h := hB (NegativeLine.normalizedLineMap eA eB f x) (NegativeLine.normalizedLineMap eA eB f y)
  change G (eB (eB.symm (f (eA x)))) (eB (eB.symm (f (eA y)))) = _ at h
  rw [eB.apply_symm_apply, eB.apply_symm_apply] at h
  exact h.symm.trans ((hf (eA x) (eA y)).trans (hA x y))

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem normalizedEmbeddedIsometry_last_ne_zero
    (H K : Matrix (Fin 3) (Fin 3) E) (u : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E))
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian K (u x) (u y) = Datum.RankThreePELDatum.matrixHermitian H x y)
    (τ : E →ₐ[ℚ] ℂ) (β : ℂ)
    (eA eB : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (hA : ∀ x y, Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map τ) (eA x) (eA y) =
      Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x y)
    (hB : ∀ x y, Complex.HermitianMatrixForm.complexHermitianMatrixForm (K.map τ) (eB x) (eB y) =
      Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x y)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : (Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0) :
    NegativeLine.normalizedLineMap eA eB (EmbeddedLinearGroup.embeddedLinearIso u τ) (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0 := by
  apply NegativeLine.diagonalIsometry_last_ne_zero β _ ?_ z hz
  exact normalizedHermitian_isometry _ _ _ eA eB (EmbeddedLinearGroup.embeddedLinearIso u τ) hA hB
    (Hermitian.IsometryEmbedding.hermitianIsometry_embedding H K u.toLinearMap hu τ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.HermitianTransport
