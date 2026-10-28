import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceIsometries

/-! # Isometry Determinant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryDeterminant.TraceReconstruction

noncomputable section

/-! Isometries of the reconstructed form have CM norm-one determinant.
The calculation uses the actual reconstructed matrix, and works for all
nondegenerate rational forms with the CM adjoint relation. -/

variable {E ι : Type*} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Fintype ι] [DecidableEq ι]

def matrixPairing (H : Matrix ι ι E) (x y : ι → E) : E :=
  ∑ i, ∑ j, x i * H i j * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (y j)

theorem matrixPairing_basis (H : Matrix ι ι E) (i j : ι) :
    matrixPairing H (Pi.single i 1) (Pi.single j 1) = H i j := by
  classical
  simp [matrixPairing, Pi.single_apply]

theorem matrixPairing_isometry_equation (H : Matrix ι ι E) (g : (ι → E) ≃ₗ[E] (ι → E))
    (hg : ∀ x y, matrixPairing H (g x) (g y) = matrixPairing H x y) :
    (LinearMap.toMatrix' g.toLinearMap).transpose * H *
      (LinearMap.toMatrix' g.toLinearMap).map (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E) = H := by
  ext i j
  have h := (hg (Pi.single i 1) (Pi.single j 1)).trans (matrixPairing_basis H i j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact h

theorem matrixPairing_isometry_det_norm_one (H : Matrix ι ι E) (hH : H.det ≠ 0)
    (g : (ι → E) ≃ₗ[E] (ι → E))
    (hg : ∀ x y, matrixPairing H (g x) (g y) = matrixPairing H x y) :
    LinearMap.det g.toLinearMap * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (LinearMap.det g.toLinearMap) = 1 := by
  have h := congrArg Matrix.det (matrixPairing_isometry_equation H g hg)
  have hm : ((LinearMap.toMatrix' g.toLinearMap).map (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E)).det =
      ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (LinearMap.toMatrix' g.toLinearMap).det :=
    ((ComplexMultiplication.CM.TraceForm.cmFieldConjugation E).toRingHom.map_det _).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hm, LinearMap.det_toMatrix'] at h
  apply mul_right_cancel₀ hH
  calc
    (LinearMap.det g.toLinearMap * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (LinearMap.det g.toLinearMap)) * H.det =
        LinearMap.det g.toLinearMap * H.det * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (LinearMap.det g.toLinearMap) := by ring
    _ = H.det := h
    _ = 1 * H.det := (one_mul _).symm

theorem rational_isometry_det_norm_one (ξ : E) (hξ : ξ ≠ 0)
    (ψ : (ι → E) →ₗ[ℚ] (ι → E) →ₗ[ℚ] ℚ) (hψ : Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ)
    (hnd : ∀ x, (∀ y, ψ x y = 0) → x = 0) (g : (ι → E) ≃ₗ[E] (ι → E))
    (hg : ∀ x y, ψ (g x) (g y) = ψ x y) :
    LinearMap.det g.toLinearMap * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (LinearMap.det g.toLinearMap) = 1 := by
  apply matrixPairing_isometry_det_norm_one (Matrices.TraceReconstruction.hermitianMatrix ξ ψ hψ)
    (Matrices.TraceReconstruction.hermitianMatrix_det_ne_zero ξ hξ ψ hψ hnd) g
  intro x y
  change (∑ i, ∑ j, g x i * Matrices.TraceReconstruction.hermitianMatrix ξ ψ hψ i j * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (g y j)) =
    ∑ i, ∑ j, x i * Matrices.TraceReconstruction.hermitianMatrix ξ ψ hψ i j * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (y j)
  rw [Matrices.TraceReconstruction.hermitianMatrix_evaluate, Matrices.TraceReconstruction.hermitianMatrix_evaluate]
  exact (TraceIsometries.TraceReconstruction.hermitianCoefficient_isometry_iff ξ hξ ψ ψ g.toLinearMap).mpr hg x y

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryDeterminant.TraceReconstruction
