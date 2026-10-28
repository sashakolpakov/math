import Mathlib

/-! # Padic Integral Bound -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralBound.Local

noncomputable section

/-! A finite collection of number-field coefficients is integral under
every q-adic embedding for all sufficiently large rational primes. -/

open scoped Classical

theorem finite_coefficients_padic_integral_bound
    {E : Type*} [Field E] [NumberField E]
    {I : Type*} [Fintype I] (a : I → E) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], N < q →
      ∀ (σ : E →+* ℚ_[q]) (i : I), ‖σ (a i)‖ ≤ 1 := by
  have hex (i : I) : ∃ m : nonZeroDivisors ℤ, IsIntegral ℤ ((m : ℤ) • a i) := by
    exact IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) (Rₘ := ℚ) (a i) (Algebra.IsIntegral.isIntegral (a i))
  choose m hm using hex
  let N := 1 + ∑ i, (m i : ℤ).natAbs
  refine ⟨N, Nat.add_pos_left Nat.zero_lt_one _, ?_⟩
  intro q hq hlarge σ i
  have hmi : (m i : ℤ).natAbs < q := by
    have hs : (m i : ℤ).natAbs ≤ ∑ j, (m j : ℤ).natAbs :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j : ℤ).natAbs) (Finset.mem_univ i)
    exact lt_of_le_of_lt (hs.trans (Nat.le_add_left _ _)) hlarge
  have hcop : q.Coprime (m i : ℤ).natAbs := (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero (m i))) hmi)
  have hn : ‖((m i : ℤ) : ℚ_[q])‖ = 1 := by
    simpa only [norm_natAbs] using (Padic.norm_natCast_eq_one_iff.mpr hcop)
  have hi : IsIntegral (ℤ_[q]) (σ ((m i : ℤ) • a i)) :=
    ((hm i).map σ.toIntAlgHom).tower_top
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  have hbnd : ‖σ ((m i : ℤ) • a i)‖ ≤ 1 := by
    rw [← hb]
    exact b.property
  simpa only [zsmul_eq_mul, map_mul, map_intCast, norm_mul, hn, one_mul] using hbnd

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralBound.Local
