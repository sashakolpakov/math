import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! # Prime Depth -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PrimeDepth

/-! Every level at least three contains either an odd prime or the square of two, at the depth needed by prime-order congruence inflation. -/

theorem level_exists_prime_depth (N : ℕ) (hN : 3 ≤ N) :
    ∃ q r : ℕ, q.Prime ∧ 0 < r ∧ r + 2 ≤ r * q ∧ q ^ r ∣ N := by
  by_cases h4 : 4 ∣ N
  · exact ⟨2, 2, by decide, by decide, by decide, h4⟩
  · by_cases h2 : 2 ∣ N
    · obtain ⟨m, hm⟩ := h2
      have hm1 : m ≠ 1 := by intro he; rw [he] at hm; omega
      obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
      have hq2 : q ≠ 2 := by
        intro he
        rw [he] at hqm
        obtain ⟨t, ht⟩ := hqm
        apply h4
        refine ⟨t, ?_⟩
        rw [hm, ht]
        omega
      have hq3 : 3 ≤ q := by have := hq.two_le; omega
      have hmN : m ∣ N := ⟨2, hm.trans (Nat.mul_comm 2 m)⟩
      exact ⟨q, 1, hq, by decide, by omega, by simpa only [pow_one] using hqm.trans hmN⟩
    · obtain ⟨q, hq, hqN⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
      have hq2 : q ≠ 2 := by intro he; exact h2 (he ▸ hqN)
      have hq3 : 3 ≤ q := by have := hq.two_le; omega
      exact ⟨q, 1, hq, by decide, by omega, by simpa only [pow_one] using hqN⟩

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PrimeDepth
