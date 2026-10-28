import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutParameters

namespace OAI.Algorithms

/-! The rank budget used by attained-signature counting.  The number of
serialized raw rows is deliberately absent: only their rational rank enters. -/
namespace SubexponentialSAT.SqrtLog.LayoutBudget

open scoped BigOperators

/-- Clear the exact rational spectral/packing budget without rounding rank. -/
theorem rank_budget_rat (n M B r L κ : ℕ)
    (hB : 0 < B) (hr : 0 < r) (hL : 0 < L)
    (hM : M ≤ B * n)
    (hκ : (κ : ℚ) ≤ 2 * (1 / (32 * B * r * L ^ 2 : ℕ) : ℚ) * M) :
    16 * (r : ℚ) * (L : ℚ)^2 * κ ≤ n := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hd : (0 : ℚ) < 32 * B * r * (L : ℚ)^2 := by positivity
  have hm : (M : ℚ) ≤ B * n := by exact_mod_cast hM
  have hdiv : (κ : ℚ) ≤ (2 * M) / (32 * B * r * (L : ℚ)^2) := by
    convert hκ using 1 ; push_cast ; ring
  have hmul := (le_div_iff₀ hd).mp hdiv
  have hc : (16 * (r : ℚ) * (L : ℚ)^2 * κ) * B ≤ (n : ℚ) * B := by
    nlinarith
  nlinarith

theorem rank_budget_nat (n M B r L κ : ℕ)
    (hB : 0 < B) (hr : 0 < r) (hL : 0 < L)
    (hM : M ≤ B * n)
    (hκ : (κ : ℚ) ≤ 2 * (1 / (32 * B * r * L ^ 2 : ℕ) : ℚ) * M) :
    16 * r * L^2 * κ ≤ n := by
  exact_mod_cast rank_budget_rat n M B r L κ hB hr hL hM hκ

theorem rank_budget_real (n M B r L κ : ℕ)
    (hB : 0 < B) (hr : 0 < r) (hL : 0 < L)
    (hM : M ≤ B * n)
    (hκ : (κ : ℚ) ≤ 2 * (1 / (32 * B * r * L ^ 2 : ℕ) : ℚ) * M) :
    16 * (r : ℝ) * (L : ℝ)^2 * κ ≤ n := by
  exact_mod_cast rank_budget_nat n M B r L κ hB hr hL hM hκ

/-- Direct interface from the sum of actual per-head ranks to the cost
assembly's real-valued premise, using the shared executable schedule. -/
theorem scheduled_total_rank_le_real {G : Type*} [Fintype G]
    (n M B : ℕ) (κ : G → ℕ) (hB : 0 < B) (hM : M ≤ B * n)
    (hκ : (∑ g, (κ g : ℚ)) ≤ 2 * Asymptotic.layoutEpsilon n B * M) :
    16 * (Asymptotic.layoutR n : ℝ) * (Asymptotic.L n : ℝ)^2 *
      (∑ g, (κ g : ℝ)) ≤ n := by
  have hr : 0 < Asymptotic.layoutR n := by
    have := Asymptotic.layoutR_ge_two n
    omega
  have hs : ((∑ g, κ g : ℕ) : ℚ) ≤
      2 * (1 / (32 * B * Asymptotic.layoutR n * Asymptotic.L n ^ 2 : ℕ) : ℚ) * M := by
    simpa only [Nat.cast_sum, Asymptotic.layoutEpsilon] using hκ
  simpa only [Nat.cast_sum] using
    rank_budget_real n M B (Asymptotic.layoutR n) (Asymptotic.L n)
      (∑ g, κ g) hB hr (Asymptotic.L_pos n) hM hs

end SubexponentialSAT.SqrtLog.LayoutBudget

end OAI.Algorithms
