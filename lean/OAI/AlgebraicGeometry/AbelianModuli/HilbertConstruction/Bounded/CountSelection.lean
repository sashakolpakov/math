import Mathlib.Algebra.BigOperators.Fin

/-! # Count Selection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.CountSelection

noncomputable section

/-! A prescribed number of objects can be selected from finitely many
bins whenever the sum of their capacities is large enough. -/
open scoped BigOperators

theorem exists_bounded_counts_with_sum {n : ℕ} (a : Fin n → ℕ) (k : ℕ)
    (hk : k ≤ ∑ i, a i) : ∃ b : Fin n → ℕ, (∀ i, b i ≤ a i) ∧ ∑ i, b i = k := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := by simpa using hk
    exact ⟨a, fun _ => le_rfl, by simp [hk0]⟩
  | succ n ih =>
    let c := min (a 0) k
    have htail : k - c ≤ ∑ i : Fin n, a i.succ := by
      rw [Fin.sum_univ_succ] at hk
      dsimp [c]
      omega
    obtain ⟨b, hb, hsum⟩ := ih (fun i => a i.succ) (k - c) htail
    refine ⟨Fin.cons c b, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact min_le_left _ _
      · exact hb j
    · rw [Fin.sum_univ_succ]
      change c + ∑ i, b i = k
      rw [hsum]
      exact Nat.add_sub_of_le (min_le_right _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.CountSelection
