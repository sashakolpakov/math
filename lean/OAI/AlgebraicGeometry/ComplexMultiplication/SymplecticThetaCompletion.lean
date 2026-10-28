import OAI.AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel
import OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCovariance

/-! # Symplectic Theta Completion -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Completion and first-coefficient covariance in symplectic coordinates

The Jacobi substitution is the actual matrix `J⁻ᵀ`, with `J = CZ + D`.
The proved inverse-imaginary-matrix identity cancels the quadratic factor
`exp (π i zᵗ J⁻¹ C z)`. The only remaining premise of the covariance
deductions is the uncompleted functional equation for the stated pair of
inputs. This file does not assert that equation or congruence descent.
-/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def SymplecticThetaCompletion.CM.complexMatrixBilinear (M : Matrix ι ι ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i : ι, ∑ j : ι,
    (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).smulRight
      ((ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).smulRight (M i j))

omit [DecidableEq ι] in
theorem SymplecticThetaCompletion.CM.complexMatrixBilinear_apply (M : Matrix ι ι ℂ) (z w : ι → ℂ) :
    SymplecticThetaCompletion.CM.complexMatrixBilinear M z w = z ⬝ᵥ (M *ᵥ w) := by
  simp [SymplecticThetaCompletion.CM.complexMatrixBilinear, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm]

theorem SymplecticThetaCompletion.CM.complexify_real_matrix_inv (M : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    (M.map (algebraMap ℝ ℂ))⁻¹ = M⁻¹.map (algebraMap ℝ ℂ) := by
  apply Matrix.inv_eq_right_inv
  change ((algebraMap ℝ ℂ).mapMatrix M) * ((algebraMap ℝ ℂ).mapMatrix M⁻¹) = 1
  rw [← map_mul, Matrix.mul_nonsing_inv _ hM, map_one]

theorem CMSiegelMatrix.CM.SiegelMatrix.completionForm_quadratic (Z : CMSiegelMatrix.CM.SiegelMatrix ι) (z w : ι → ℂ) :
    Z.completionForm z w = ((Real.pi : ℂ) / 2) * (z ⬝ᵥ ((CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹ *ᵥ w)) := by
  cases Subsingleton.elim (inferInstance : DecidableEq ι) (Classical.typeDecidableEq ι)
  let Y : Matrix ι ι ℝ := fun i j => (Z.matrix i j).im
  have hY : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).mp Z.imaginary_posDef.isUnit
  have hinv : (CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹ = Y⁻¹.map (algebraMap ℝ ℂ) :=
    SymplecticThetaCompletion.CM.complexify_real_matrix_inv Y hY
  rw [hinv]
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply,
    Complex.coe_algebraMap, mul_assoc] using! Z.completionForm_apply z w

omit [DecidableEq ι] in
theorem SymplecticThetaCompletion.CM.bilinear_matrix_pullback (K M : Matrix ι ι ℂ) (z : ι → ℂ) :
    (K *ᵥ z) ⬝ᵥ (M *ᵥ (K *ᵥ z)) = z ⬝ᵥ ((Kᵀ * M * K) *ᵥ z) := by
  symm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

variable (g : CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : CMSiegelMatrix.CM.SiegelMatrix ι)

def CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  ((g.complexify.denominator Z.matrix)⁻¹ᵀ).mulVecLin.toContinuousLinearMap

theorem CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply (z : ι → ℂ) :
    g.jacobiChange Z z = (g.complexify.denominator Z.matrix)⁻¹ᵀ *ᵥ z := rfl

def CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm : (ι → ℂ) →L[ℂ] (ι → ℂ) →L[ℂ] ℂ :=
  ((Real.pi : ℂ) * Complex.I) •
    SymplecticThetaCompletion.CM.complexMatrixBilinear ((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C)

theorem CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm_apply (z w : ι → ℂ) :
    g.thetaCorrectionForm Z z w = (Real.pi : ℂ) * Complex.I *
      (z ⬝ᵥ (((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C) *ᵥ w)) := by
  simp only [CMSymplecticSiegel.CM.SymplecticBlocks.thetaCorrectionForm, _root_.smul_apply, SymplecticThetaCompletion.CM.complexMatrixBilinear_apply, smul_eq_mul]

/-- The actual completed exponent transforms by the negative of the
quadratic exponent in the classical theta functional equation. -/
theorem CMSymplecticSiegel.CM.SymplecticBlocks.completion_correction_identity (z : ι → ℂ) :
    (g.transformSiegel Z).completionForm (g.jacobiChange Z z) (g.jacobiChange Z z) +
      g.thetaCorrectionForm Z z z = Z.completionForm z z := by
  have hpull :
      (g.jacobiChange Z z) ⬝ᵥ ((CMSymplecticSiegel.CM.matrixImaginary (g.transformSiegel Z).matrix)⁻¹ *ᵥ
        (g.jacobiChange Z z)) =
      z ⬝ᵥ ((CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹ *ᵥ z) - (2 * Complex.I) *
        (z ⬝ᵥ (((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C) *ᵥ z)) := by
    rw [g.jacobiChange_apply, SymplecticThetaCompletion.CM.bilinear_matrix_pullback, transpose_transpose]
    change z ⬝ᵥ (((g.complexify.denominator Z.matrix)⁻¹ *
      (CMSymplecticSiegel.CM.matrixImaginary (g.complexify.fractional Z.matrix))⁻¹ *
      (g.complexify.denominator Z.matrix)⁻¹ᵀ) *ᵥ z) = _
    rw [g.inverse_imaginary_pullback_siegel Z, Matrix.sub_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [CMSiegelMatrix.CM.SiegelMatrix.completionForm_quadratic, Z.completionForm_quadratic,
    g.thetaCorrectionForm_apply, hpull]
  ring

theorem CMSymplecticSiegel.CM.SymplecticBlocks.completedThetaSeries_covariance (S T : Set (ThetaCoordinates.CM.thetaCoordinateLattice ι)) (c : ℂ)
    (htransform : ∀ z,
      (g.transformSiegel Z).phase.thetaSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι)
          T (g.jacobiChange Z z) =
        c * (ThetaCompletion.CM.thetaCompletionFactor (g.thetaCorrectionForm Z) z *
          Z.phase.thetaSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S z))
    (z : ι → ℂ) :
    (g.transformSiegel Z).completedThetaSeriesOn T (g.jacobiChange Z z) =
      c * Z.completedThetaSeriesOn S z :=
  ThetaCovariance.CM.theta_completion_covariance (g.jacobiChange Z) Z.completionForm
    (g.transformSiegel Z).completionForm (g.thetaCorrectionForm Z) c _ _ htransform
    (g.completion_correction_identity Z) z

theorem CMSymplecticSiegel.CM.SymplecticBlocks.firstThetaCoefficient_symplectic_covariance
    (S T : Set (ThetaCoordinates.CM.thetaCoordinateLattice ι)) (c : ℂ)
    (htransform : ∀ z,
      (g.transformSiegel Z).phase.thetaSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι)
          T (g.jacobiChange Z z) =
        c * (ThetaCompletion.CM.thetaCompletionFactor (g.thetaCorrectionForm Z) z *
          Z.phase.thetaSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S z)) :
    (CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient T (g.transformSiegel Z).matrix).comp (g.jacobiChange Z) =
      c • CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient S Z.matrix :=
  Z.firstThetaCoefficient_covariance (g.transformSiegel Z) S T
    (g.jacobiChange Z) (g.thetaCorrectionForm Z) c htransform

end

end OAI.AlgebraicGeometry.ComplexMultiplication
