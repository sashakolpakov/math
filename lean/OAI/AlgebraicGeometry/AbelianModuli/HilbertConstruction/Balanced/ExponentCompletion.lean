import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentFiniteGeneration
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Exponent Completion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentCompletion

noncomputable section

/-! A strictly positive balanced exponent vector can complete any
finite monomial degree to a common degree, after taking a sufficiently
large power. This supplies the denominator completion for frame charts. -/
open scoped BigOperators Classical
universe u v
variable {κ : Type u} [Fintype κ] {ι : Type v}

theorem monomialMultiDegree_nsmul (w : κ → ι → ℕ) (a : κ → ℕ) (k : ℕ) (i : ι) :
    ExponentFiniteGeneration.monomialMultiDegree w (k • a) i = k * ExponentFiniteGeneration.monomialMultiDegree w a i := by
  simp only [ExponentFiniteGeneration.monomialMultiDegree, Pi.smul_apply, nsmul_eq_mul, Nat.cast_id, Nat.mul_assoc, Finset.mul_sum]

theorem positiveExponent_exists_strict_completion (a : κ → ℕ) (ha : ∀ j, 0 < a j)
    (b : κ → ℕ) : ∃ k : ℕ, 0 < k ∧ ∃ c : κ → ℕ, (∀ j, 0 < c j) ∧ c + b = k • a := by
  let k := (∑ j, b j) + 1
  have hk : 0 < k := Nat.succ_pos _
  have hb (j : κ) : b j < k * a j := by
    have hsum : b j ≤ ∑ j, b j := Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ _)
    have hka : k ≤ k * a j := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (Nat.succ_le_of_lt (ha j))
    exact (Nat.lt_succ_of_le hsum).trans_le hka
  refine ⟨k, hk, fun j => k * a j - b j, fun j => Nat.sub_pos_of_lt (hb j), ?_⟩
  funext j
  exact Nat.sub_add_cancel (hb j).le

theorem positiveBalancedExponent_degree_completion (w : κ → ι → ℕ)
    (a : κ → ℕ) (ha : ∀ j, 0 < a j) (hbal : a ∈ ExponentFiniteGeneration.balancedExponentMonoid w) (b : κ → ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∃ c : κ → ℕ, (∀ j, 0 < c j) ∧ c + b = k • a ∧
      ∀ i j, ExponentFiniteGeneration.monomialMultiDegree w c i + ExponentFiniteGeneration.monomialMultiDegree w b i =
        k * ExponentFiniteGeneration.monomialMultiDegree w a j := by
  obtain ⟨k, hk, c, hc, he⟩ := positiveExponent_exists_strict_completion a ha b
  refine ⟨k, hk, c, hc, he, ?_⟩
  intro i j
  rw [← ExponentFiniteGeneration.monomialMultiDegree_add, he, monomialMultiDegree_nsmul,
    (ExponentFiniteGeneration.mem_balancedExponentMonoid_iff w a).mp hbal i j]

theorem balanced_completion_of_same_degree (w : κ → ι → ℕ)
    (a b c d : κ → ℕ) (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid w)
    (he : c + b = a) (hd : ∀ i, ExponentFiniteGeneration.monomialMultiDegree w d i = ExponentFiniteGeneration.monomialMultiDegree w b i) :
    c + d ∈ ExponentFiniteGeneration.balancedExponentMonoid w := by
  apply (ExponentFiniteGeneration.mem_balancedExponentMonoid_iff _ _).mpr
  intro i j
  simp only [ExponentFiniteGeneration.monomialMultiDegree_add, hd]
  rw [← ExponentFiniteGeneration.monomialMultiDegree_add, ← ExponentFiniteGeneration.monomialMultiDegree_add, he]
  exact (ExponentFiniteGeneration.mem_balancedExponentMonoid_iff _ _).mp ha i j

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentCompletion
