import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-! # Reflection Matrix -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionMatrix

/-! Determinants of the actual rank-three reflection matrices.
Two normalized rank-one reflections have determinant one. -/

variable {k : Type*} [CommRing k]

def rankThreeReflectionMatrix (v w : Fin 3 → k) : Matrix (Fin 3) (Fin 3) k :=
  1 - (2 : k) • Matrix.of (fun i j => v i * w j)

theorem rankThreeReflectionMatrix_det (v w : Fin 3 → k)
    (h : ∑ i, v i * w i = 1) : (rankThreeReflectionMatrix v w).det = -1 := by
  have hd : (rankThreeReflectionMatrix v w).det =
      1 - 2 * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2) := by
    simp [rankThreeReflectionMatrix, Matrix.det_fin_three]
    ring
  have hs : v 0 * w 0 + v 1 * w 1 + v 2 * w 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using h
  rw [hd, hs]
  ring

theorem rankThreeReflectionMatrix_mul_det
    (v w a b : Fin 3 → k)
    (hvw : ∑ i, v i * w i = 1) (hab : ∑ i, a i * b i = 1) :
    (rankThreeReflectionMatrix v w * rankThreeReflectionMatrix a b).det = 1 := by
  rw [Matrix.det_mul, rankThreeReflectionMatrix_det v w hvw,
    rankThreeReflectionMatrix_det a b hab]
  ring

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionMatrix
