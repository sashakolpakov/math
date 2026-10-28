import OAI.NumberTheory.Quaternion.Arithmetic.Norm
import Mathlib.Algebra.QuaternionBasis

/-! # Split Matrices -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SplitMatrices

noncomputable section

section

/-! A solution of the binary norm equation gives an explicit
two-dimensional matrix representation of a quaternion algebra. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra _root_.Matrix

variable {K : Type*} [Field K]

def quaternionSplittingBasis (a b x y : K) (h : x ^ 2 - a * y ^ 2 = b) :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) K) a 0 b where
  i := !![0, a; 1, 0]
  j := !![x, -a * y; y, -x]
  k := !![a * y, -a * x; x, -a * y]
  i_mul_i := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals linear_combination h
  i_mul_j := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def quaternionSplittingMap (a b x y : K) (h : x ^ 2 - a * y ^ 2 = b) :
    ℍ[K,a,b] →ₐ[K] Matrix (Fin 2) (Fin 2) K := (quaternionSplittingBasis a b x y h).liftHom

theorem quaternionSplittingMap_apply (a b x y : K) (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[K,a,b]) :
    quaternionSplittingMap a b x y h q =
      !![q.re + q.imJ * x + q.imK * a * y, a * q.imI - a * q.imJ * y - a * q.imK * x;
         q.imI + q.imJ * y + q.imK * x, q.re - q.imJ * x - q.imK * a * y] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [quaternionSplittingMap, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift,
      quaternionSplittingBasis, Matrix.algebraMap_matrix_apply] <;> ring

theorem quaternionSplittingMap_det (a b x y : K) (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[K,a,b]) :
    (quaternionSplittingMap a b x y h q).det = Norm.quaternionNorm a b q := by
  rw [quaternionSplittingMap_apply, Matrix.det_fin_two, Norm.quaternionNorm_formula]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linear_combination (a * q.imK ^ 2 - q.imJ ^ 2) * h

end

/-! The explicit quaternion splitting representation is a faithful
algebra isomorphism when the structure constants are nonzero. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra _root_.Matrix

variable {K : Type*} [Field K] [CharZero K]

theorem quaternionSplittingMap_eq_zero (a b x y : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[K,a,b])
    (hq : quaternionSplittingMap a b x y h q = 0) : q = 0 := by
  rw [quaternionSplittingMap_apply] at hq
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hq
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hq
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hq
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hq
  change q.re + q.imJ * x + q.imK * a * y = 0 at h00
  change a * q.imI - a * q.imJ * y - a * q.imK * x = 0 at h01
  change q.imI + q.imJ * y + q.imK * x = 0 at h10
  change q.re - q.imJ * x - q.imK * a * y = 0 at h11
  have hr : (2 : K) * q.re = 0 := by linear_combination h00 + h11
  have hi : (2 * a) * q.imI = 0 := by linear_combination h01 + a * h10
  have hj : (2 * b) * q.imJ = 0 := by
    linear_combination x * h00 - x * h11 - a * y * h10 + y * h01 - 2 * q.imJ * h
  have hk : (2 * a * b) * q.imK = 0 := by
    linear_combination a * x * h10 - x * h01 - a * y * h00 + a * y * h11 - 2 * a * q.imK * h
  apply QuaternionAlgebra.ext
  · exact (mul_eq_zero.mp hr).resolve_left two_ne_zero
  · exact (mul_eq_zero.mp hi).resolve_left (mul_ne_zero two_ne_zero ha)
  · exact (mul_eq_zero.mp hj).resolve_left (mul_ne_zero two_ne_zero hb)
  · exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero (mul_ne_zero two_ne_zero ha) hb)

theorem quaternionSplittingMap_injective (a b x y : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) : Function.Injective (quaternionSplittingMap a b x y h) := by
  intro q r he
  apply sub_eq_zero.mp
  apply quaternionSplittingMap_eq_zero a b x y ha hb h
  rw [map_sub, he, sub_self]

def quaternionSplittingEquiv (a b x y : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) : ℍ[K,a,b] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  AlgEquiv.ofBijective (quaternionSplittingMap a b x y h) ⟨quaternionSplittingMap_injective a b x y ha hb h,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (show Module.finrank K ℍ[K,a,b] = Module.finrank K (Matrix (Fin 2) (Fin 2) K) by
        rw [QuaternionAlgebra.finrank_eq_four]
        rw [Module.finrank_matrix]
        norm_num)
      (f := (quaternionSplittingMap a b x y h).toLinearMap)).mp
        (quaternionSplittingMap_injective a b x y ha hb h)⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.SplitMatrices
