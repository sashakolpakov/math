import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeBinomialDivisibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingIntegerBinomial
import Mathlib.Algebra.BigOperators.Intervals

/-! # Prime Power Binomial Linearization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimePowerBinomialLinearization

noncomputable section

/-! A prime-order power has a linear term and a remainder divisible by one further prime power in any ring. -/

open scoped BigOperators

universe u

variable {R : Type u} [Ring R]

theorem primePower_binomialLinearization (x : R) (q r : ℕ) (hq : q.Prime) (hr : 0 < r)
    (hsize : r + 2 ≤ r * q) :
    ∃ z : R, (1 + (q ^ r) • x) ^ q = 1 + (q ^ (r + 1)) • x + (q ^ (r + 2)) • z := by
  let t (i : ℕ) : R := (q.choose i * (q ^ r) ^ i) • x ^ i
  let z := ∑ i ∈ Finset.Ico 2 (q + 1), ((q.choose i * (q ^ r) ^ i) / q ^ (r + 2)) • x ^ i
  have hle : 2 ≤ q + 1 := by have := hq.two_le; omega
  have hfirst : ∑ i ∈ Finset.range 2, t i = 1 + (q ^ (r + 1)) • x := by
    simp [t, Finset.sum_range_succ, pow_succ']
  have hrest : ∑ i ∈ Finset.Ico 2 (q + 1), t i = (q ^ (r + 2)) • z := by
    change _ = (q ^ (r + 2)) • ∑ i ∈ Finset.Ico 2 (q + 1),
      ((q.choose i * (q ^ r) ^ i) / q ^ (r + 2)) • x ^ i
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hd := PrimeBinomialDivisibility.primeBinomial_highTerm_divisible q r i hq hr (Finset.mem_Ico.mp hi).1
      (Nat.le_of_lt_succ (Finset.mem_Ico.mp hi).2) hsize
    dsimp [t]
    rw [← mul_smul, Nat.mul_div_cancel' hd]
  refine ⟨z, ?_⟩
  have he := (Finset.sum_range_add_sum_Ico t hle).symm
  exact (RingIntegerBinomial.ringPower_integerBinomial x (q ^ r) q).trans
    (he.trans (congrArg₂ (fun a b : R => a + b) hfirst hrest))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimePowerBinomialLinearization
