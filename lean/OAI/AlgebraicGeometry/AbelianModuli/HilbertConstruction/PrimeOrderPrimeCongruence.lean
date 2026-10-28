import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeOrderCongruenceInflation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoprimeFiniteOrderCongruence

/-! # Prime Order Prime Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeOrderPrimeCongruence

noncomputable section

/-! Every prime-order element satisfying a sufficiently deep prime congruence satisfies all powers of that prime, including when the two primes agree. -/

universe u

variable {R : Type u} [Ring R] [IsAddTorsionFree R]

theorem primeOrder_primeCongruence_allPowers (u : R) (p q r : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hr : 0 < r) (hsize : r + 2 ≤ r * q) (hu : u ^ p = 1)
    (h : ∃ x : R, (q ^ r) • x = u - 1) (k : ℕ) :
    ∃ y : R, (q ^ k) • y = u - 1 := by
  by_cases he : p = q
  · subst p
    exact PrimeOrderCongruenceInflation.primeOrder_congruence_allPowers u q r hq hr hsize hu h k
  · have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr he
    have hd : q ∣ q ^ r := by
      simpa only [pow_one] using pow_dvd_pow q (Nat.succ_le_of_lt hr)
    obtain ⟨x, hx⟩ := h
    have hqcong : ∃ y : R, q • y = u - 1 := by
      refine ⟨(q ^ r / q) • x, ?_⟩
      rw [← mul_smul, Nat.mul_div_cancel' hd]
      exact hx
    exact CoprimeFiniteOrderCongruence.coprime_finiteOrder_congruence_allPowers u q p hq.ne_zero hcop hu hqcong k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrimeOrderPrimeCongruence
