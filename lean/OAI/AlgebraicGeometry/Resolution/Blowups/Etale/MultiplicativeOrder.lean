import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalTruncation
import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialMultiplicativeOrder

/-! # Multiplicative Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MultiplicativeOrder.Construction

noncomputable section

/-! Exact multiplicativity for arbitrary sections of étale local coordinate rings. -/

theorem ideal_mem_iff_of_sub_mem {R : Type*} [CommRing R] (I : Ideal R)
    {s t : R} (h : s - t ∈ I) : s ∈ I ↔ t ∈ I := by
  constructor
  · intro hs
    simpa only [sub_sub_cancel] using I.sub_mem hs h
  · intro ht
    simpa only [sub_add_cancel] using I.add_mem h ht

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Reflection of polynomial power containment, including the zeroth power. -/
theorem etale_local_polynomial_mem_pow_iff_all (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (n : ℕ) (p : MvPolynomial σ K) :
    algebraMap (MvPolynomial σ K) (Localization.AtPrime q) p ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n ↔ p ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ n := by
  by_cases hn : n = 0
  · simp only [hn, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  · exact LocalTruncation.Construction.etale_local_polynomial_mem_pow_iff x q n hn p

/-- Exact local orders add for arbitrary local sections, using their finite
polynomial approximations. No polynomial-origin condition is imposed on the sections. -/
theorem etale_local_exact_order_mul (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (s t : Localization.AtPrime q) (a b : ℕ)
    (hs : s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ a)
    (hs1 : s ∉ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (a + 1))
    (ht : t ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b)
    (ht1 : t ∉ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b + 1)) :
    s * t ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (a + b) ∧
      s * t ∉ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (a + b + 1) := by
  let M := IsLocalRing.maximalIdeal (Localization.AtPrime q)
  let φ := algebraMap (MvPolynomial σ K) (Localization.AtPrime q)
  obtain ⟨p, hp⟩ := LocalTruncation.Construction.etale_local_exists_polynomial_approximation x q (a + b + 1)
    (by omega) s
  obtain ⟨r, hr⟩ := LocalTruncation.Construction.etale_local_exists_polynomial_approximation x q (a + b + 1)
    (by omega) t
  have hpiff (n : ℕ) (hn : n ≤ a + b + 1) :
      s ∈ M ^ n ↔ p ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ n :=
    (ideal_mem_iff_of_sub_mem (M ^ n) ((Ideal.pow_le_pow_right hn) hp)).trans
      (etale_local_polynomial_mem_pow_iff_all x q n p)
  have hriff (n : ℕ) (hn : n ≤ a + b + 1) :
      t ∈ M ^ n ↔ r ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ n :=
    (ideal_mem_iff_of_sub_mem (M ^ n) ((Ideal.pow_le_pow_right hn) hr)).trans
      (etale_local_polynomial_mem_pow_iff_all x q n r)
  have hpr := PolynomialMultiplicativeOrder.Construction.polynomial_point_exact_order_mul x p r a b
    ((hpiff a (by omega)).mp hs) (fun h => hs1 ((hpiff (a + 1) (by omega)).mpr h))
    ((hriff b (by omega)).mp ht) (fun h => ht1 ((hriff (b + 1) (by omega)).mpr h))
  refine ⟨?_, ?_⟩
  · simpa only [pow_add] using Ideal.mul_mem_mul hs ht
  · have hprod : s * t - φ (p * r) ∈ M ^ (a + b + 1) := by
      have heq : s * t - φ (p * r) = (s - φ p) * t + φ p * (t - φ r) := by
        rw [map_mul]
        ring
      rw [heq]
      exact (M ^ (a + b + 1)).add_mem
        ((M ^ (a + b + 1)).mul_mem_right t hp)
        ((M ^ (a + b + 1)).mul_mem_left (φ p) hr)
    intro hst
    exact hpr.2 ((etale_local_polynomial_mem_pow_iff_all x q (a + b + 1) (p * r)).mp
      ((ideal_mem_iff_of_sub_mem (M ^ (a + b + 1)) hprod).mp hst))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MultiplicativeOrder.Construction
