import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding
import OAI.Geometry.ComplexBall.PrescribedSignsB

/-! # Embedded Bilinear Isometry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedBilinearIsometry

noncomputable section

/-! The original Hermitian isometry preserves the bilinear pairing
between the two paired complex embedding blocks. -/

open OAI.Geometry.ComplexBall.PrescribedSignsB

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

omit [NumberField E] [NumberField.IsCMField E] in
theorem embeddedLinearIso_conjugate (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (σ : E →ₐ[ℚ] ℂ) (x : Fin 3 → ℂ) :
    EmbeddedLinearGroup.embeddedLinearIso g (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ) x = star (EmbeddedLinearGroup.embeddedLinearIso g σ (star x)) := by
  funext i
  simp only [EmbeddedLinearGroup.embeddedLinearIso_apply, Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  change star (σ (LinearMap.toMatrix' g.toLinearMap i j)) * x j = x j * star (σ (LinearMap.toMatrix' g.toLinearMap i j))
  exact mul_comm _ _

omit [NumberField E] [NumberField.IsCMField E] in
theorem hermitianForm_as_localB {I : Type} (σ : I → E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (i : I) (x y : Fin 3 → ℂ) :
    Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map (σ i)) x y = Geometry.ComplexBall.PrescribedSignsB.localB σ H i x (star y) :=
  Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply _ x y

theorem localB_embedded_isometry {I : Type} (σ : I → E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hg : ∀ x y, Datum.RankThreePELDatum.matrixHermitian H (g x) (g y) = Datum.RankThreePELDatum.matrixHermitian H x y)
    (i : I) (x y : Fin 3 → ℂ) :
    Geometry.ComplexBall.PrescribedSignsB.localB σ H i (EmbeddedLinearGroup.embeddedLinearIso g (σ i) x) (EmbeddedLinearGroup.embeddedLinearIso g (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ i)) y) =
      Geometry.ComplexBall.PrescribedSignsB.localB σ H i x y := by
  let f := EmbeddedLinearGroup.embeddedLinearIso g (σ i)
  have hl : Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map (σ i)) (f x) (f (star y)) =
      Geometry.ComplexBall.PrescribedSignsB.localB σ H i (f x) (EmbeddedLinearGroup.embeddedLinearIso g (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ i)) y) :=
    (hermitianForm_as_localB σ H i (f x) (f (star y))).trans
      (congrArg (Geometry.ComplexBall.PrescribedSignsB.localB σ H i (f x)) (embeddedLinearIso_conjugate g (σ i) y).symm)
  have hr : Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map (σ i)) x (star y) = Geometry.ComplexBall.PrescribedSignsB.localB σ H i x y :=
    (hermitianForm_as_localB σ H i x (star y)).trans (congrArg (Geometry.ComplexBall.PrescribedSignsB.localB σ H i x) (star_star y))
  exact hl.symm.trans ((Hermitian.IsometryEmbedding.hermitianIsometry_embedding H H g.toLinearMap hg (σ i) x (star y)).trans hr)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedBilinearIsometry
