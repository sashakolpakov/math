import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.QuadraticUnitary

/-! # Active Rotation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveRotation.Approximation

noncomputable section

/-! A rational rotation of the two positive coordinates preserves every
diagonal Hermitian form diag(1,1,b) and carries the first binary roots
to the second binary roots. -/

open scoped Classical _root_.Matrix
open _root_.Matrix.SpecialLinearGroup

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.QuadraticUnitary

variable (R : Type*) [CommRing R]

def positiveRotation : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL R :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

def positiveRotationInverse : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL R :=
  ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem positiveRotation_inv : (positiveRotation R)⁻¹ = positiveRotationInverse R := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (positiveRotation R).val * (positiveRotationInverse R).val = (1 : Matrix (Fin 3) (Fin 3) R)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveRotation, positiveRotationInverse, Matrix.mul_apply, Fin.sum_univ_three]

def positiveRotationUnitary (c : R →+* R) (b : R) : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU c b :=
  ⟨positiveRotation R, by
    rw [Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitary_iff_columns]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [positiveRotation, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient, Fin.sum_univ_three]⟩

theorem positiveRotation_map {S : Type*} [CommRing S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (positiveRotation R) = positiveRotation S := by
  apply Subtype.ext
  change (positiveRotation R).val.map f = (positiveRotation S).val
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [positiveRotation]

theorem positiveRotation_forward (a : R) :
    positiveRotation R * transvection (show (0 : Fin 3) ≠ 2 by decide) a * (positiveRotation R)⁻¹ =
      transvection (show (1 : Fin 3) ≠ 2 by decide) a := by
  rw [positiveRotation_inv]
  apply Subtype.ext
  change (positiveRotation R).val * (transvection (show (0 : Fin 3) ≠ 2 by decide) a).val *
    (positiveRotationInverse R).val = (transvection (show (1 : Fin 3) ≠ 2 by decide) a).val
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveRotation, positiveRotationInverse, transvection_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.one_apply]

theorem positiveRotation_backward (a : R) :
    positiveRotation R * transvection (show (2 : Fin 3) ≠ 0 by decide) a * (positiveRotation R)⁻¹ =
      transvection (show (2 : Fin 3) ≠ 1 by decide) a := by
  rw [positiveRotation_inv]
  apply Subtype.ext
  change (positiveRotation R).val * (transvection (show (2 : Fin 3) ≠ 0 by decide) a).val *
    (positiveRotationInverse R).val = (transvection (show (2 : Fin 3) ≠ 1 by decide) a).val
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveRotation, positiveRotationInverse, transvection_coe,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.one_apply]

theorem activeBinaryBlock_forward (a : R) :
    Quaternion.QuadraticUnitary.activeBinaryBlock (transvection (show (0 : Fin 2) ≠ 1 by decide) a) =
      transvection (show (0 : Fin 3) ≠ 2 by decide) a := by
  apply Subtype.ext
  change Quaternion.QuadraticUnitary.activeBinaryMatrix (transvection (show (0 : Fin 2) ≠ 1 by decide) a).val =
    (transvection (show (0 : Fin 3) ≠ 2 by decide) a).val
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Quaternion.QuadraticUnitary.activeBinaryMatrix, transvection_coe]

theorem activeBinaryBlock_backward (a : R) :
    Quaternion.QuadraticUnitary.activeBinaryBlock (transvection (show (1 : Fin 2) ≠ 0 by decide) a) =
      transvection (show (2 : Fin 3) ≠ 0 by decide) a := by
  apply Subtype.ext
  change Quaternion.QuadraticUnitary.activeBinaryMatrix (transvection (show (1 : Fin 2) ≠ 0 by decide) a).val =
    (transvection (show (2 : Fin 3) ≠ 0 by decide) a).val
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Quaternion.QuadraticUnitary.activeBinaryMatrix, transvection_coe]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveRotation.Approximation
