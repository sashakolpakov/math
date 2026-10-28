import Mathlib.Data.Nat.Prime.Basic

/-! # Prime Bounds -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeBounds.CM

/-! Combine positive rational-prime exclusion bounds. -/

theorem combine
    (P Q R : (q : ℕ) → [Fact q.Prime] → Prop)
    (hP : ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N → P q)
    (hQ : ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N → Q q)
    (h : ∀ (q : ℕ) [Fact q.Prime], P q → Q q → R q) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N → R q := by
  obtain ⟨N, hN, hp⟩ := hP
  obtain ⟨M, hM, hq⟩ := hQ
  refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
  intro q _ hqm
  have hm := Nat.coprime_mul_iff_right.mp hqm
  exact h q (hp q hm.1) (hq q hm.2)

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeBounds.CM
