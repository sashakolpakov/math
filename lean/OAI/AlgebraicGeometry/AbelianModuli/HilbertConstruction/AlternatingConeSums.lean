import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! # Alternating Cone Sums -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlternatingConeSums

section

/-! The finite alternating dimension sum retains exactly the final outgoing boundary term. -/

theorem alternating_dimension_telescope (x h b : ℕ → ℤ)
    (hzero : x 0 = h 0 + b 0)
    (hsucc : ∀ q, x (q + 1) = h (q + 1) + b q + b (q + 1)) (N : ℕ) :
    (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * x q) =
      (∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q * h q) + (-1 : ℤ) ^ N * b N := by
  induction N with
  | zero => simpa using hzero
  | succ N ih =>
      rw [Finset.sum_range_succ (n := N + 1), Finset.sum_range_succ (n := N + 1),
        ih, hsucc N, pow_succ]
      ring

end

/-! Alternating sums of cone terms, with the final zero terms accounted for. -/

theorem alternating_cone_sum (a b c : ℕ → ℤ)
    (hzero : c 0 = b 0) (hstep : ∀ n, c (n + 1) = a n + b (n + 1))
    (r : ℕ) (ha : a (r + 1) = 0) (hb : b (r + 1) = 0) :
    (∑ n ∈ Finset.range (r + 2), (-1 : ℤ) ^ n * c n) =
      (∑ n ∈ Finset.range (r + 1), (-1 : ℤ) ^ n * b n) -
        (∑ n ∈ Finset.range (r + 1), (-1 : ℤ) ^ n * a n) := by
  have hz : c 0 = (b 0 - a 0) + a 0 := by rw [hzero]; ring
  have hs (n : ℕ) : c (n + 1) = (b (n + 1) - a (n + 1)) + a n + a (n + 1) := by
    rw [hstep n]
    ring
  have h := alternating_dimension_telescope c (fun n => b n - a n) a hz hs (r + 1)
  calc
    _ = ∑ n ∈ Finset.range (r + 2), (-1 : ℤ) ^ n * (b n - a n) := by
      simpa only [ha, mul_zero, add_zero] using h
    _ = ∑ n ∈ Finset.range (r + 1), (-1 : ℤ) ^ n * (b n - a n) := by
      rw [Finset.sum_range_succ (n := r + 1), ha, hb]
      simp only [sub_self, mul_zero, add_zero]
    _ = _ := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlternatingConeSums
