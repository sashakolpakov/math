import OAI.NumberTheory.Quaternion.Arithmetic.Norm
import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Unitary Matrix -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.UnitaryMatrix

noncomputable section

/-! The quaternion algebra (a,-b) acts on a binary Hermitian space.
The matrix and determinant formulas retain the specified quadratic root. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E]
  (a b : F) (δ : E) (hδ : δ ^ 2 = algebraMap F E a)

theorem matrixScalar_apply (t : F) (M : Matrix (Fin 2) (Fin 2) E) (i j : Fin 2) :
    (t • M) i j = algebraMap F E t * M i j := Algebra.smul_def t (M i j)

def unitaryQuaternionBasis :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) E) a 0 (-b) where
  i := !![δ, 0; 0, -δ]
  j := !![0, -algebraMap F E b; 1, 0]
  k := !![0, -δ * algebraMap F E b; -δ, 0]
  i_mul_i := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def (A := E), ← pow_two, hδ]
  j_mul_j := by
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def (A := E)]
  i_mul_j := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

def unitaryQuaternionMap : ℍ[F,a,-b] →ₐ[F] Matrix (Fin 2) (Fin 2) E :=
  (unitaryQuaternionBasis a b δ hδ).liftHom

theorem unitaryQuaternionMap_apply (q : ℍ[F,a,-b]) :
    unitaryQuaternionMap a b δ hδ q =
      !![algebraMap F E q.re + δ * algebraMap F E q.imI,
         -algebraMap F E b * (algebraMap F E q.imJ + δ * algebraMap F E q.imK);
         algebraMap F E q.imJ - δ * algebraMap F E q.imK,
         algebraMap F E q.re - δ * algebraMap F E q.imI] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [unitaryQuaternionMap, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
      unitaryQuaternionBasis, Matrix.algebraMap_matrix_apply, Algebra.smul_def (A := E)] <;> ring

theorem unitaryQuaternionMap_det (q : ℍ[F,a,-b]) :
    (unitaryQuaternionMap a b δ hδ q).det =
      algebraMap F E (NumberTheory.Quaternion.Arithmetic.Norm.quaternionNorm a (-b) q) := by
  rw [unitaryQuaternionMap_apply, Matrix.det_fin_two, NumberTheory.Quaternion.Arithmetic.Norm.quaternionNorm_formula]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    map_add, map_sub, map_mul, map_neg, map_pow]
  linear_combination
    -(algebraMap F E q.imI ^ 2 + algebraMap F E b * algebraMap F E q.imK ^ 2) * hδ

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.UnitaryMatrix
