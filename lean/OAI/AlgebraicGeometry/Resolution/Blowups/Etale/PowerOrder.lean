import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MultiplicativeOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.Order

/-! # Power Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PowerOrder.Construction

noncomputable section

/-! Exact power tests for arbitrary ideals in étale local coordinate rings. -/

theorem ideal_mem_pow_iff_of_exact_order {R : Type*} [CommRing R]
    (I : Ideal R) (s : R) (d n : ℕ) (hd : s ∈ I ^ d) (hd1 : s ∉ I ^ (d + 1)) :
    s ∈ I ^ n ↔ n ≤ d := by
  constructor
  · intro hn
    by_contra h
    exact hd1 ((Ideal.pow_le_pow_right (by omega : d + 1 ≤ n)) hn)
  · intro hn
    exact (Ideal.pow_le_pow_right hn) hd

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

theorem etale_local_exact_order_pow (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (s : Localization.AtPrime q) (d e : ℕ)
    (hs : s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ d)
    (hs1 : s ∉ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (d + 1)) :
    s ^ e ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (d * e) ∧
      s ^ e ∉ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (d * e + 1) := by
  induction e with
  | zero =>
    simp only [pow_zero, Nat.mul_zero, zero_add, pow_one, Ideal.one_eq_top,
      Submodule.mem_top, true_and]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime q)).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  | succ e ih =>
    simpa only [pow_succ, Nat.mul_succ] using
      MultiplicativeOrder.Construction.etale_local_exact_order_mul x q (s ^ e) s (d * e) d ih.1 ih.2 hs hs1

include σ K in
omit [IsAlgClosed K] in
/-- Every nonzero local section has a finite exact order. -/
theorem etale_local_exists_exact_order (q : Ideal S) [q.IsMaximal]
    (s : Localization.AtPrime q) (hs : s ≠ 0) :
    ∃ d : ℕ, s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ d ∧
      s ∉ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (d + 1) := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ K) S
  obtain ⟨d, hd, hd1⟩ := Blowups.Ideal.Order.Construction.exists_idealAdicOrder
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (Ideal.span {s})
    (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime q)).ne_top
    (fun h => hs (Ideal.span_singleton_eq_bot.mp h))
  exact ⟨d, (Ideal.span_singleton_le_iff_mem _).mp hd,
    fun h => hd1 ((Ideal.span_singleton_le_iff_mem _).mpr h)⟩

/-- A positive power has order at least the correspondingly multiplied control
if and only if the section has the original order bound. -/
theorem etale_local_pow_mem_pow_iff (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (s : Localization.AtPrime q) (b e : ℕ)
    (he : 0 < e) :
    s ^ e ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b * e) ↔
      s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b := by
  by_cases hs : s = 0
  · simp only [hs, zero_pow (Nat.ne_of_gt he), Submodule.zero_mem]
  · obtain ⟨d, hd, hd1⟩ := etale_local_exists_exact_order (σ := σ) (K := K) q s hs
    obtain ⟨hde, hde1⟩ := etale_local_exact_order_pow x q s d e hd hd1
    rw [ideal_mem_pow_iff_of_exact_order _ _ (d * e) (b * e) hde hde1,
      ideal_mem_pow_iff_of_exact_order _ _ d b hd hd1]
    exact Nat.mul_le_mul_right_iff he

/-- Exact power scaling for arbitrary local ideals, including the zero ideal. -/
theorem etale_local_ideal_pow_le_pow_iff (x : σ → K) (q : Ideal S) [q.IsMaximal]
    [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (J : Ideal (Localization.AtPrime q))
    (b e : ℕ) (he : 0 < e) :
    J ^ e ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b * e) ↔
      J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b := by
  constructor
  · intro h s hs
    exact (etale_local_pow_mem_pow_iff x q s b e he).mp (h (Ideal.pow_mem_pow hs e))
  · intro h
    simpa only [pow_mul] using pow_le_pow_left' h e

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PowerOrder.Construction
