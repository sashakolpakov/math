import Mathlib

/-! # Central Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CentralParameters

noncomputable section

/-! Prove the complete CentralConstraint central-parameter constraint. Only its
original finite-order, occurrence, and normalized Satake hypotheses are
used. No statement stub is imported. -/

open scoped Classical

theorem occurring_finite_order_value
    {K H V : Type*} [Field K] [CommRing H] [Algebra K H]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : H →ₐ[K] Module.End K V) (χ : H →ₐ[K] K)
    (hoccurs : (⨅ h : H, (ρ h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : H) (N : ℕ) (hN : (ρ h) ^ N = 1) : (χ h) ^ N = 1 := by
  have hgen : (ρ h).HasUnifEigenvalue (χ h) ⊤ := by
    intro hz
    exact hoccurs (eq_bot_iff.mpr ((iInf_le _ h).trans hz.le))
  have heigen : (ρ h).HasEigenvalue (χ h) := hgen.lt zero_lt_one
  obtain ⟨x, hx⟩ := heigen.exists_hasEigenvector
  have hp := hx.pow_apply N
  rw [hN] at hp
  apply smul_left_injective K hx.2
  simpa only [Module.End.one_apply, one_smul] using hp.symm

theorem triple_sum_permutation {K : Type*} [CommRing K] (β : Fin 3 → K) (σ : Equiv.Perm (Fin 3)) :
    β (σ 0) + β (σ 1) + β (σ 2) = β 0 + β 1 + β 2 := by
  simpa only [Fin.sum_univ_three] using Equiv.sum_comp σ β

theorem triple_pair_permutation {K : Type*} [Field K] [CharZero K]
    (β : Fin 3 → K) (σ : Equiv.Perm (Fin 3)) :
    β (σ 0) * β (σ 1) + β (σ 0) * β (σ 2) + β (σ 1) * β (σ 2) =
      β 0 * β 1 + β 0 * β 2 + β 1 * β 2 := by
  have hs := triple_sum_permutation β σ
  have hsq := triple_sum_permutation (fun i => β i ^ 2) σ
  have h2 : (2 : K) *
      (β (σ 0) * β (σ 1) + β (σ 0) * β (σ 2) + β (σ 1) * β (σ 2)) =
    (2 : K) * (β 0 * β 1 + β 0 * β 2 + β 1 * β 2) := by
    linear_combination (β (σ 0) + β (σ 1) + β (σ 2) + β 0 + β 1 + β 2) * hs - hsq
  exact mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0) h2

theorem triple_prod_permutation {K : Type*} [CommRing K] (β : Fin 3 → K) (σ : Equiv.Perm (Fin 3)) :
    β (σ 0) * β (σ 1) * β (σ 2) = β 0 * β 1 * β 2 := by
  simpa only [Fin.prod_univ_three] using Equiv.prod_comp σ β

theorem central_constraint_on_full_satake_extensions
    {K H V : Type*}
    [Field K] [CharZero K] [Algebra ℚ K] [IsAlgClosed K]
    [CommRing H] [Algebra K H]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : H →ₐ[K] Module.End K V) (χ : H →ₐ[K] K)
    (q : ℕ) (hq : q.Prime) (r e : K) (hr : r ^ 2 = (q : K))
    (he : e ≠ 0) (he_alg : IsAlgebraic ℚ e)
    (T₁ T₂ T₃ C₀ : H) (α : Fin 3 → K)
    (hoccurs : (⨅ h : H, (ρ h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hcentral : ∃ N : ℕ, 0 < N ∧ (ρ T₃) ^ N = 1 ∧ (ρ C₀) ^ N = 1)
    (hT₁ : χ T₁ = (q : K) * (α 0 + α 1 + α 2))
    (hT₂ : χ T₂ = (q : K) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2))
    (hT₃ : χ T₃ = α 0 * α 1 * α 2)
    (hprojective : ∃ a : K, a ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3),
      ∀ i, α i = a * (![r, r⁻¹, e] : Fin 3 → K) (σ i)) :
    ∃ b : K, ∃ σ : Equiv.Perm (Fin 3),
      b ≠ 0 ∧ IsAlgebraic ℚ b ∧ (∀ i, IsAlgebraic ℚ (α i)) ∧
      (∀ i, χ C₀ * α i = b * (![r, r⁻¹, e] : Fin 3 → K) (σ i)) ∧
      b ^ 3 * e = (χ C₀) ^ 3 * χ T₃ ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * e) ^ n = 1 ∧
        ∀ γ : K ≃ₐ[ℚ] K, ((γ b) ^ 3 * γ e) ^ n = 1) ∧
      χ (C₀ * T₁) = (q : K) * b * (r + r⁻¹ + e) ∧
      χ (C₀ ^ 2 * T₂) = (q : K) * b ^ 2 * (r * r⁻¹ + r * e + r⁻¹ * e) := by
  obtain ⟨N, hN, hNT, hNC⟩ := hcentral
  have hT := occurring_finite_order_value ρ χ hoccurs T₃ N hNT
  have hC := occurring_finite_order_value ρ χ hoccurs C₀ N hNC
  have hC0 : χ C₀ ≠ 0 := by intro h; simp [h, hN.ne'] at hC
  have hTalg : IsAlgebraic ℚ (χ T₃) :=
    IsAlgebraic.of_pow hN (hT.symm ▸ isAlgebraic_one)
  have hCalg : IsAlgebraic ℚ (χ C₀) :=
    IsAlgebraic.of_pow hN (hC.symm ▸ isAlgebraic_one)
  have hr0 : r ≠ 0 := by
    intro h
    exact (Nat.cast_ne_zero.mpr hq.ne_zero : (q : K) ≠ 0) (by simpa [h] using hr.symm)
  have hralg : IsAlgebraic ℚ r :=
    IsAlgebraic.of_pow (n := 2) (by decide) (hr.symm ▸ isAlgebraic_natCast q)
  obtain ⟨a, ha, σ, hα⟩ := hprojective
  let β : Fin 3 → K := ![r, r⁻¹, e]
  have hp := triple_prod_permutation β σ
  have hs := triple_sum_permutation β σ
  have ht := triple_pair_permutation β σ
  have hdet : a ^ 3 * e = χ T₃ := by
    rw [hT₃, hα 0, hα 1, hα 2]
    change a ^ 3 * e = (a * β (σ 0)) * (a * β (σ 1)) * (a * β (σ 2))
    calc
      _ = a ^ 3 * (β 0 * β 1 * β 2) := by simp [β, hr0]
      _ = a ^ 3 * (β (σ 0) * β (σ 1) * β (σ 2)) := congrArg (a ^ 3 * ·) hp.symm
      _ = _ := by ring
  have ha3 : a ^ 3 = χ T₃ * e⁻¹ := by
    simpa only [div_eq_mul_inv] using (eq_div_iff he).mpr hdet
  have haalg : IsAlgebraic ℚ a :=
    IsAlgebraic.of_pow (n := 3) (by decide) (ha3.symm ▸ hTalg.mul he_alg.inv)
  let b := χ C₀ * a
  have hbdet : b ^ 3 * e = (χ C₀) ^ 3 * χ T₃ := by dsimp [b]; rw [mul_pow, mul_assoc, hdet]
  have hbn : (b ^ 3 * e) ^ N = 1 := by
    rw [hbdet, mul_pow, hT, mul_one, ← pow_mul, Nat.mul_comm 3 N, pow_mul, hC, one_pow]
  refine ⟨b, σ, mul_ne_zero hC0 ha, hCalg.mul haalg, ?_, ?_, hbdet, ⟨N, hN, hbn, ?_⟩, ?_, ?_⟩
  · intro i
    rw [hα i]
    apply haalg.mul
    have hβ : ∀ k : Fin 3, IsAlgebraic ℚ (β k) := by
      intro k
      fin_cases k
      · exact hralg
      · exact hralg.inv
      · exact he_alg
    exact hβ (σ i)
  · intro i
    rw [hα i]
    exact (mul_assoc _ _ _).symm
  · intro γ
    simpa only [map_pow, map_mul, map_one] using congrArg γ hbn
  · rw [map_mul, hT₁, hα 0, hα 1, hα 2]
    change χ C₀ * ((q : K) * (a * β (σ 0) + a * β (σ 1) + a * β (σ 2))) =
      (q : K) * (χ C₀ * a) * (β 0 + β 1 + β 2)
    linear_combination (q : K) * χ C₀ * a * hs
  · rw [map_mul, map_pow, hT₂, hα 0, hα 1, hα 2]
    change (χ C₀) ^ 2 * ((q : K) *
      ((a * β (σ 0)) * (a * β (σ 1)) + (a * β (σ 0)) * (a * β (σ 2)) +
        (a * β (σ 1)) * (a * β (σ 2)))) =
      (q : K) * (χ C₀ * a) ^ 2 * (β 0 * β 1 + β 0 * β 2 + β 1 * β 2)
    linear_combination (q : K) * (χ C₀) ^ 2 * a ^ 2 * ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CentralParameters
