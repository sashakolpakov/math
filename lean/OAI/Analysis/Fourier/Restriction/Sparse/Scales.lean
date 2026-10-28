import OAI.Analysis.Fourier.Restriction.Sparse.Cover
import Mathlib.Tactic.GCongr

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def sparseScale (M D j : ℕ) : ℝ :=
  (4 * ((M : ℝ) + 1)) ^ ((3 * D + 1) ^ j)

theorem sparseScale_succ (M D j : ℕ) :
    sparseScale M D (j + 1) = sparseScale M D j ^ (3 * D + 1) := by
  simp only [sparseScale, pow_succ, pow_mul]

theorem sparseScale_base_le (M D j : ℕ) :
    4 * ((M : ℝ) + 1) ≤ sparseScale M D j := by
  apply le_self_pow₀
  · have h := Nat.cast_nonneg (α := ℝ) M
    linarith
  · exact (pow_pos (by omega : 0 < 3 * D + 1) j).ne'

theorem sparseScale_ge_four (M D j : ℕ) : 4 ≤ sparseScale M D j :=
  (by have h := Nat.cast_nonneg (α := ℝ) M; linarith : 4 ≤ 4 * ((M : ℝ) + 1)).trans
    (sparseScale_base_le M D j)

theorem sparseScale_step (M D j : ℕ) (hD : 0 < D) :
    2 * sparseScale M D j ≤ sparseScale M D (j + 1) := by
  rw [sparseScale_succ]
  have hfour := sparseScale_ge_four M D j
  have hsq : 2 * sparseScale M D j ≤ sparseScale M D j ^ 2 := by nlinarith
  exact hsq.trans (pow_le_pow_right₀ (by linarith) (by omega))

/-- The next scale dominates the polynomial sparsity requirement for
at most `M` balls of radius `4*sparseScale M D j`. -/
theorem sparseScale_separation (M D j : ℕ) :
    (4 * sparseScale M D j) ^ D * (M : ℝ) ^ D ≤ sparseScale M D (j + 1) := by
  have hfour := sparseScale_ge_four M D j
  have hM : (M : ℝ) ≤ sparseScale M D j := by
    have hb := sparseScale_base_le M D j
    have h0 := Nat.cast_nonneg (α := ℝ) M
    linarith
  have hsq : 4 * sparseScale M D j ≤ sparseScale M D j ^ 2 := by nlinarith
  calc
    _ ≤ (sparseScale M D j ^ 2) ^ D * sparseScale M D j ^ D := by gcongr
    _ = sparseScale M D j ^ (3 * D) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ sparseScale M D j ^ (3 * D + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    _ = sparseScale M D (j + 1) := (sparseScale_succ M D j).symm

theorem sparseScale_mono (M D : ℕ) : Monotone (sparseScale M D) := by
  intro i j hij
  apply pow_le_pow_right₀ (by have h := Nat.cast_nonneg (α := ℝ) M; linarith)
  exact pow_le_pow_right₀ (by omega : 1 ≤ 3 * D + 1) hij

end OAI.Analysis.Fourier.Restriction
