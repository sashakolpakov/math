import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentCompletion

/-! # Supported Exponent Completion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedExponentCompletion

noncomputable section

/-! A balanced exponent vector completes any monomial supported on its
positive entries. The same complement balances every equal-degree numerator. -/
open scoped BigOperators Classical
universe u v
variable {κ : Type u} [Fintype κ] {ι : Type v}

theorem supportedExponent_exists_completion (a b : κ → ℕ)
    (hab : ∀ j, b j ≠ 0 → 0 < a j) :
    ∃ k : ℕ, 0 < k ∧ ∃ c : κ → ℕ, c + b = k • a := by
  let k := (∑ j, b j) + 1
  have hb (j : κ) : b j ≤ k * a j := by
    by_cases hj : b j = 0
    · rw [hj]
      exact Nat.zero_le _
    · have hsum : b j ≤ ∑ j, b j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ _)
      have hka : k ≤ k * a j := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (Nat.succ_le_of_lt (hab j hj))
      exact (hsum.trans (Nat.le_succ _)).trans hka
  refine ⟨k, Nat.succ_pos _, fun j => k * a j - b j, ?_⟩
  funext j
  exact Nat.sub_add_cancel (hb j)

omit [Fintype κ] in
theorem exponent_complement_of_le {a b : κ → ℕ} (h : b ≤ a) :
    ∃ c : κ → ℕ, c + b = a := by
  refine ⟨fun j => a j - b j, ?_⟩
  funext j
  exact Nat.sub_add_cancel (h j)

theorem supportedBalancedExponent_exists_completion (w : κ → ι → ℕ)
    (a b : κ → ℕ) (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid w)
    (hab : ∀ j, b j ≠ 0 → 0 < a j) :
    ∃ k : ℕ, 0 < k ∧ ∃ c : κ → ℕ, c + b = k • a ∧
      k • a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid w ∧
      ∀ d : κ → ℕ, (∀ i, Balanced.ExponentFiniteGeneration.monomialMultiDegree w d i = Balanced.ExponentFiniteGeneration.monomialMultiDegree w b i) →
        c + d ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid w := by
  obtain ⟨k, hk, c, hc⟩ := supportedExponent_exists_completion a b hab
  have hka : k • a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid w := (Balanced.ExponentFiniteGeneration.balancedExponentMonoid w).nsmul_mem ha k
  exact ⟨k, hk, c, hc, hka, fun d hd => Balanced.ExponentCompletion.balanced_completion_of_same_degree w _ _ _ _ hka hc hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedExponentCompletion
