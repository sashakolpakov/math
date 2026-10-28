import Mathlib.Data.Nat.Prime.Basic

/-! # Prime Threshold -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeThreshold.CM

/-! Convert a positive excluded-divisor bound to a prime-size threshold. -/

theorem of_coprime (P : (q : ℕ) → [Fact q.Prime] → Prop)
    (h : ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N → P q) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], N < q → P q := by
  obtain ⟨N, hN, hp⟩ := h
  exact ⟨N, hN, fun q _ hq => hp q (Nat.coprime_of_lt_prime hN.ne' hq Fact.out)⟩

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeThreshold.CM
