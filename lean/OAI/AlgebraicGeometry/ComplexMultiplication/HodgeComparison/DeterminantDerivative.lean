import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseCoefficientCancellation
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Determinant Derivative -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DeterminantDerivative.CM.Construction

noncomputable section

/-! Jacobi's determinant formula for differentiable matrix coefficients. -/

variable {ι 𝕜 E : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def determinantMultilinear : ContinuousMultilinearMap 𝕜 (fun _ : ι => ι → 𝕜) 𝕜 where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := by
    change Continuous (fun M : ι → ι → 𝕜 => Matrix.det (Matrix.of M))
    simp only [Matrix.det_apply', Matrix.of_apply]
    fun_prop

theorem determinant_derivative_rows (M : E → Matrix ι ι 𝕜) {x : E}
    (hM : ∀ i, DifferentiableAt ℝ (fun y => M y i) x) (u : E) :
    fderiv ℝ (fun y => (M y).det) x u =
      ∑ i, ((M x).updateRow i (fderiv ℝ (fun y => M y i) x u)).det := by
  have hd := HasFDerivAt.multilinear_comp
    ((determinantMultilinear (ι := ι) (𝕜 := 𝕜)).restrictScalars ℝ)
    (fun i => (hM i).hasFDerivAt)
  have hv := congrArg (fun L : E →L[ℝ] 𝕜 => L u) hd.fderiv
  change fderiv ℝ (fun y => (M y).det) x u = _ at hv
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply] at hv
  exact hv

theorem determinant_updateRow_inverse (M H : Matrix ι ι 𝕜)
    (hM : IsUnit M.det) (i : ι) :
    (M.updateRow i (H i)).det = (H * M⁻¹) i i * M.det := by
  have hr : H i = ∑ j, (H * M⁻¹) i j • M j := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change H i k = ((H * M⁻¹) * M) i k
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.mul_one]
  rw [hr, Matrix.det_updateRow_sum, smul_eq_mul]

theorem determinant_derivative_trace (M : E → Matrix ι ι 𝕜) {x : E}
    (hM : ∀ i, DifferentiableAt ℝ (fun y => M y i) x)
    (hdet : IsUnit (M x).det) (u : E) :
    fderiv ℝ (fun y => (M y).det) x u =
      (M x).det * ((M x)⁻¹ * Matrix.of (fun i => fderiv ℝ (fun y => M y i) x u)).trace := by
  rw [determinant_derivative_rows M hM]
  calc
    _ = ∑ i, (Matrix.of (fun j => fderiv ℝ (fun y => M y j) x u) * (M x)⁻¹) i i *
        (M x).det := by
      apply Finset.sum_congr rfl
      intro i _
      exact determinant_updateRow_inverse (M x)
        (Matrix.of (fun j => fderiv ℝ (fun y => M y j) x u)) hdet i
    _ = _ := by
      rw [← Finset.sum_mul]
      change (Matrix.trace (Matrix.of (fun i => fderiv ℝ (fun y => M y i) x u) * (M x)⁻¹)) *
        (M x).det = _
      rw [Matrix.trace_mul_comm, mul_comm]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DeterminantDerivative.CM.Construction
