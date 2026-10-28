import OAI.Analysis.Fourier.Restriction.BallCover
import Mathlib

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The explicit sparse covering constant has only a small power dependence
on the number of occupied unit balls. -/
theorem sparse_cover_growth_bound {M α : ℝ} (hM : 1 ≤ M) (hα : 0 ≤ α)
    (N k : ℕ) :
    (3 * N * M ^ (1 / (N : ℝ))) * (5 * (4 * (M + 1)) ^ k) ^ α ≤
      (3 * N * (5 * (8 : ℝ) ^ k) ^ α) * M ^ (1 / (N : ℝ) + k * α) := by
  have hM0 : 0 < M := by linarith
  have hbase : 4 * (M + 1) ≤ 8 * M := by linarith
  calc
    _ ≤ (3 * N * M ^ (1 / (N : ℝ))) * (5 * (8 * M) ^ k) ^ α := by
      gcongr
    _ = (3 * N * M ^ (1 / (N : ℝ))) *
        ((5 * (8 : ℝ) ^ k) ^ α * M ^ ((k : ℝ) * α)) := by
      rw [mul_pow, ← mul_assoc, Real.mul_rpow (by positivity) (pow_nonneg hM0.le k),
        ← Real.rpow_natCast_mul hM0.le]
    _ = _ := by
      rw [Real.rpow_add hM0]
      ring

/-- One first chooses the number of covering layers, then a sufficiently
small local loss. This is the quantitative exponent selection in epsilon removal. -/
theorem exists_sparse_cover_loss {ε : ℝ} (hε : 0 < ε) (D : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∃ α : ℝ, 0 < α ∧
      1 / (N : ℝ) + (((3 * D + 1) ^ N : ℕ) : ℝ) * α < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hN0 : 0 < (N : ℝ) := (div_pos (by norm_num) hε).trans hN
  have hNnat : 0 < N := by exact_mod_cast hN0
  have hhalf : 1 / (N : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hN0).mpr
    have H := (div_lt_iff₀ hε).mp hN
    nlinarith
  let k : ℝ := (((3 * D + 1) ^ N : ℕ) : ℝ)
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast pow_pos (by omega : 0 < 3 * D + 1) N
  refine ⟨N, hNnat, ε / (4 * k), div_pos hε (by positivity), ?_⟩
  change 1 / (N : ℝ) + k * (ε / (4 * k)) < ε
  have he : k * (ε / (4 * k)) = ε / 4 := by field_simp
  rw [he]
  linarith

end OAI.Analysis.Fourier.Restriction
