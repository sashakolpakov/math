import OAI.LinearAlgebra.Moore.Inverse

/-! Positivity of the Moore linearization through the faithful representation. -/

namespace OAI.LinearAlgebra.Moore

open Matrix
open scoped MatrixOrder ComplexOrder

theorem isHermitian_of_complexify {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : (complexify A).IsHermitian) : A.IsHermitian := by
  apply complexify_injective
  rw [complexify_star]
  exact hA

theorem complex_trace_mul_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (Complex.nonneg_iff.mp (hA.mul_mul_conjTranspose_same C).trace_nonneg).1

/-- An actual quaternionic inverse remains positive definite in the faithful
complex representation. -/
theorem complexify_inverse_posDef (n : ℕ)
    (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hAC : A * C = 1) :
    (complexify C).PosDef := by
  have h : complexify A * complexify C = 1 := by
    rw [← complexify_mul, hAC, complexify_one]
  rw [← Matrix.inv_eq_right_inv h]
  exact hA.inv

/-- Ellipticity of the inverse-trace linearization at matrices with positive
Moore determinant. Positive semidefinite directions have nonnegative derivative. -/
theorem mooreDifferential_nonneg (n : ℕ)
    (A D C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosDef) (hD : (complexify D).PosSemidef)
    (hAC : A * C = 1) (hCA : C * A = 1) (hdet : 0 ≤ mooreDet n A) :
    0 ≤ mooreDifferential n A D := by
  rw [mooreDifferential_inverse n A D C (isHermitian_of_complexify hA.isHermitian)
    (isHermitian_of_complexify hD.isHermitian) hAC hCA]
  apply mul_nonneg hdet
  have hC := (complexify_inverse_posDef n A C hA hAC).posSemidef
  have h := complex_trace_mul_nonneg hC hD
  rw [← complexify_mul, complexify_trace_real] at h
  linarith

end OAI.LinearAlgebra.Moore
