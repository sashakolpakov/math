import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Block Projection -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockProjection.Construction

noncomputable section

/-! The diagonal-block projection is multiplicative on matrices
preserving an ordered weight filtration. -/

open scoped Classical
open _root_.Matrix

variable {R ι α : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [LinearOrder α]

def weightBlockProjection (w : ι → α) : Matrix ι ι R →ₗ[R] Matrix ι ι R where
  toFun M i j := if w i = w j then M i j else 0
  map_add' M N := by
    ext i j
    change (if w i = w j then M i j + N i j else 0) =
      (if w i = w j then M i j else 0) + (if w i = w j then N i j else 0)
    split_ifs <;> simp
  map_smul' c M := by
    ext i j
    change (if w i = w j then c * M i j else 0) = c * (if w i = w j then M i j else 0)
    split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
theorem weightBlockProjection_apply (w : ι → α) (M : Matrix ι ι R) (i j : ι) :
    weightBlockProjection w M i j = if w i = w j then M i j else 0 := rfl

omit [DecidableEq ι] in
theorem weightBlockProjection_mul (w : ι → α) (M N : Matrix ι ι R)
    (hM : Matrix.BlockTriangular (α := OrderDual α) M w)
    (hN : Matrix.BlockTriangular (α := OrderDual α) N w) :
    weightBlockProjection w (M * N) = weightBlockProjection w M * weightBlockProjection w N := by
  ext i j
  change (if w i = w j then ∑ k, M i k * N k j else 0) =
    ∑ k, (if w i = w k then M i k else 0) * (if w k = w j then N k j else 0)
  by_cases hij : w i = w j
  · rw [ite_eq_left hij]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : w i = w k
    · rw [ite_eq_left hik, ite_eq_left (hik.symm.trans hij)]
    · rw [ite_eq_right hik, zero_mul]
      rcases lt_or_gt_of_ne hik with hlt | hgt
      · rw [hM hlt, zero_mul]
      · rw [hN (show w k < w j from hgt.trans_eq hij), mul_zero]
  · rw [ite_eq_right hij]
    symm
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : w i = w k
    · have hkj : w k ≠ w j := fun h => hij (hik.trans h)
      rw [ite_eq_right hkj, mul_zero]
    · rw [ite_eq_right hik, zero_mul]

omit [Fintype ι] in
theorem weightBlockProjection_one (w : ι → α) : weightBlockProjection w (1 : Matrix ι ι R) = 1 := by
  ext i j
  rw [weightBlockProjection_apply]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
  · rw [Matrix.one_apply_ne hij]
    split_ifs <;> rfl

omit [Fintype ι] [DecidableEq ι] in
theorem weightBlockProjection_idempotent (w : ι → α) (M : Matrix ι ι R) :
    weightBlockProjection w (weightBlockProjection w M) = weightBlockProjection w M := by
  ext i j
  simp only [weightBlockProjection_apply]
  split_ifs <;> rfl

def weightBlockProjectionHom (w : ι → α) :
    Matrix.blockTriangularSubalgebra (α := OrderDual α) R R w →ₐ[R] Matrix ι ι R where
  toFun M := weightBlockProjection w M.val
  map_zero' := map_zero _
  map_one' := weightBlockProjection_one w
  map_add' M N := map_add _ M.val N.val
  map_mul' M N := weightBlockProjection_mul w M.val N.val M.property N.property
  commutes' c := by
    change weightBlockProjection w (algebraMap R (Matrix ι ι R) c) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, weightBlockProjection_one]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockProjection.Construction
