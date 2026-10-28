import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Sum High Weight Count -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SumHighWeightCount

noncomputable section

/-! The numerical separation estimate used for stable point
configurations: zero-sum weights force enough labels above the negative
threshold determined by their positive maximum. -/
open scoped BigOperators Classical
universe u

theorem zeroSum_highWeight_count_bound {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (ha : ∑ i, a i = 0) (M : ℝ) (hM : 0 < M)
    (hmax : ∀ i, a i ≤ M) (r : ℕ) (hr : 1 ≤ r)
    (H : Finset ι) (houtside : ∀ i ∉ H, (r - 1 : ℝ) * a i ≤ -M) :
    (Fintype.card ι : ℝ) ≤ r * H.card := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ (r : ℝ) - 1 := sub_nonneg.mpr hr1
  have hterm (i : ι) : ((r : ℝ) - 1) * a i ≤
      (if i ∈ H then (r : ℝ) * M else 0) - M := by
    by_cases hi : i ∈ H
    · simp only [hi, ite_true]
      nlinarith [mul_le_mul_of_nonneg_left (hmax i) hr0]
    · simpa only [hi, ite_false, zero_sub] using houtside i hi
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hterm i)
  rw [← Finset.mul_sum, ha, mul_zero, Finset.sum_sub_distrib] at hs
  have hH : (∑ i : ι, if i ∈ H then (r : ℝ) * M else 0) =
      (H.card : ℝ) * ((r : ℝ) * M) := by
    rw [Finset.sum_ite]
    simp
  rw [hH] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith

theorem zeroSum_strictHighWeight_count {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (ha : ∑ i, a i = 0) (M : ℝ) (hM : 0 < M)
    (hmax : ∀ i, a i ≤ M) (r : ℕ) (hr : 1 ≤ r) :
    Fintype.card ι ≤ r * (Finset.univ.filter (fun i => -M < ((r : ℝ) - 1) * a i)).card := by
  have h := zeroSum_highWeight_count_bound a ha M hM hmax r hr
    (Finset.univ.filter (fun i => -M < ((r : ℝ) - 1) * a i)) (by
      intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hi)
  exact_mod_cast h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SumHighWeightCount
