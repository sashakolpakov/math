import OAI.Analysis.Fourier.Restriction.Sparse.Scales
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Choose the branching number so that a depth-`N` density decomposition
has only `O(M^(1/N))` colors per layer. -/
theorem exists_sparse_branching (M N : ℕ) (hM : 1 ≤ M) (hN : 0 < N) :
    ∃ K : ℕ, 0 < K ∧ M ≤ K ^ N ∧
      ((K + 1 : ℕ) : ℝ) ≤ 3 * (M : ℝ) ^ (1 / (N : ℝ)) := by
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let a : ℝ := (M : ℝ) ^ (1 / (N : ℝ))
  have ha : 1 ≤ a := Real.one_le_rpow hMr (one_div_nonneg.mpr hNr.le)
  have ha0 : 0 ≤ a := by linarith
  let K := Nat.floor a + 1
  have haK : a ≤ (K : ℝ) := by
    exact le_of_lt (by simpa only [K, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one a)
  have haN : a ^ N = (M : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0,
      one_div_mul_cancel (ne_of_gt hNr), Real.rpow_one]
  have hpower : (M : ℝ) ≤ (K : ℝ) ^ N := by
    rw [← haN]
    exact pow_le_pow_left₀ ha0 haK N
  have hMK : M ≤ K ^ N := by exact_mod_cast hpower
  refine ⟨K, by omega, hMK, ?_⟩
  have hfloor := Nat.floor_le ha0
  simp only [K, Nat.cast_add, Nat.cast_one]
  change (Nat.floor a : ℝ) + 1 + 1 ≤ 3 * a
  linarith

end OAI.Analysis.Fourier.Restriction
