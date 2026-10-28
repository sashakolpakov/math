import OAI.LinearAlgebra.Moore.Form
import Mathlib.Analysis.Matrix.Order

/-! Positive quaternionic matrices are finite sums of quaternionic rank-one
matrices.  The proof projects an ordinary complex positive factorization back
to the quaternionic subspace, pairing the two complex coordinates. -/

noncomputable section
namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion
open scoped MatrixOrder ComplexOrder

def quaternionProjectionEntry (a b c d : ℂ) : Quaternion ℝ :=
  ⟨a.re + d.re, a.im - d.im, b.re - c.re, b.im + c.im⟩

/-- Twice the projection onto the quaternionic matrices.  The normalization
is chosen so that a single complex rank-one matrix projects to a single
quaternionic rank-one matrix. -/
def quaternionProjection (n : ℕ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ →ₗ[ℝ]
      Matrix (Fin n) (Fin n) (Quaternion ℝ) where
  toFun A i j := quaternionProjectionEntry
    (A (i,0) (j,0)) (A (i,0) (j,1)) (A (i,1) (j,0)) (A (i,1) (j,1))
  map_add' A B := by
    apply Matrix.ext
    intro i j
    change quaternionProjectionEntry
      (A (i,0) (j,0) + B (i,0) (j,0)) (A (i,0) (j,1) + B (i,0) (j,1))
      (A (i,1) (j,0) + B (i,1) (j,0)) (A (i,1) (j,1) + B (i,1) (j,1)) =
      quaternionProjectionEntry (A (i,0) (j,0)) (A (i,0) (j,1))
        (A (i,1) (j,0)) (A (i,1) (j,1)) +
      quaternionProjectionEntry (B (i,0) (j,0)) (B (i,0) (j,1))
        (B (i,1) (j,0)) (B (i,1) (j,1))
    ext <;> simp [quaternionProjectionEntry] <;> ring
  map_smul' c A := by
    apply Matrix.ext
    intro i j
    change quaternionProjectionEntry
      (c • A (i,0) (j,0)) (c • A (i,0) (j,1))
      (c • A (i,1) (j,0)) (c • A (i,1) (j,1)) =
      c • quaternionProjectionEntry (A (i,0) (j,0)) (A (i,0) (j,1))
        (A (i,1) (j,0)) (A (i,1) (j,1))
    ext <;> simp [quaternionProjectionEntry] <;> ring

theorem quaternionProjection_apply (n : ℕ)
    (A : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) (i j : Fin n) :
    quaternionProjection n A i j = quaternionProjectionEntry
      (A (i,0) (j,0)) (A (i,0) (j,1)) (A (i,1) (j,0)) (A (i,1) (j,1)) := rfl

theorem quaternionProjection_complexify {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    quaternionProjection n (complexify A) = (2 : ℝ) • A := by
  ext i j <;> simp [quaternionProjection_apply, quaternionProjectionEntry,
    complexify, quaternionMatrix] <;> ring

theorem quaternionProjection_rankOne {n : ℕ} (z : Fin n × Fin 2 → ℂ) :
    quaternionProjection n (Matrix.vecMulVec z (star z)) =
      OAI.Analysis.Calculus.Quaternion.outer (quaternionVector z) := by
  ext i j <;>
    simp [quaternionProjection_apply, quaternionProjectionEntry, Matrix.vecMulVec, OAI.Analysis.Calculus.Quaternion.outer, quaternionVector,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem quaternionProjection_mul_conjTranspose {n : ℕ}
    {ι : Type*} [Fintype ι]
    (C : Matrix (Fin n × Fin 2) ι ℂ) :
    quaternionProjection n (C * Cᴴ) =
      ∑ k, OAI.Analysis.Calculus.Quaternion.outer (quaternionVector (fun i ↦ C i k)) := by
  have hC : C * Cᴴ = ∑ k, Matrix.vecMulVec (fun i ↦ C i k)
      (star (fun i ↦ C i k)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec, Matrix.sum_apply]
  rw [hC, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact quaternionProjection_rankOne _

/-- Every positive quaternionic Hermitian matrix is a sum of `2n` genuine
quaternionic outer products, with no nondegeneracy or rank assumption. -/
theorem exists_sum_outer_of_complexify_posSemidef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (complexify A).PosSemidef) :
    ∃ v : (Fin n × Fin 2) → Fin n → Quaternion ℝ,
      A = ∑ k, OAI.Analysis.Calculus.Quaternion.outer (v k) := by
  have hhalf : 0 ≤ (1/2 : ℝ) • complexify A :=
    (hA.smul (by norm_num : 0 ≤ (1/2 : ℝ))).nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hhalf
  let C := Bᴴ
  have hC : C * Cᴴ = (1/2 : ℝ) • complexify A := by
    simpa only [C, Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose]
      using hB.symm
  refine ⟨fun k ↦ quaternionVector (fun i ↦ C i k), ?_⟩
  rw [← quaternionProjection_mul_conjTranspose, hC, map_smul,
    quaternionProjection_complexify, smul_smul]
  norm_num

end OAI.LinearAlgebra.Moore
