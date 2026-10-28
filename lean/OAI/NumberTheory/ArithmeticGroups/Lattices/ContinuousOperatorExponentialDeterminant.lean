import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ExponentialEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixExponentialDeterminant

/-! # Continuous Operator Exponential Determinant -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousOperatorExponentialDeterminant.Construction

noncomputable section

/-! The determinant of a finite-dimensional real operator exponential
is the exponential of its trace. -/

open scoped Classical _root_.Matrix.Norms.Operator
open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

def continuousEndMatrix {m : ℕ} (b : Module.Basis (Fin m) ℝ L) :
    (L →L[ℝ] L) →ₐ[ℝ] Matrix (Fin m) (Fin m) ℝ where
  toFun A := LinearMap.toMatrix b b A.toLinearMap
  map_zero' := by simp
  map_one' := by simp
  map_add' A C := by simp
  map_mul' A C := by
    change LinearMap.toMatrix b b (A.toLinearMap.comp C.toLinearMap) = _
    exact LinearMap.toMatrix_comp b b b A.toLinearMap C.toLinearMap
  commutes' c := by
    change LinearMap.toMatrix b b (c • LinearMap.id) = algebraMap ℝ _ c
    simp [Algebra.algebraMap_eq_smul_one]

theorem continuousEndMatrix_continuous {m : ℕ} (b : Module.Basis (Fin m) ℝ L) :
    Continuous (continuousEndMatrix b) :=
  (continuousEndMatrix b).toLinearMap.continuous_of_finiteDimensional

theorem continuousOperator_exp_det (A : L →L[ℝ] L) :
    LinearMap.det (exp A).toLinearMap = exp (LinearMap.trace ℝ L A.toLinearMap) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let b := Module.finBasis ℝ L
  have he := NormedSpace.map_exp (continuousEndMatrix b) (continuousEndMatrix_continuous b) A
  have hd := congrArg Matrix.det he
  change (LinearMap.toMatrix b b (exp A).toLinearMap).det =
    (exp (LinearMap.toMatrix b b A.toLinearMap)).det at hd
  rw [LinearMap.det_toMatrix, MatrixExponentialDeterminant.Construction.matrix_exp_det, ← LinearMap.trace_eq_matrix_trace] at hd
  exact hd

theorem continuousOperator_exp_det_one_of_trace_zero (A : L →L[ℝ] L)
    (hA : LinearMap.trace ℝ L A.toLinearMap = 0) : LinearMap.det (exp A).toLinearMap = 1 := by
  rw [continuousOperator_exp_det, hA, exp_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousOperatorExponentialDeterminant.Construction
