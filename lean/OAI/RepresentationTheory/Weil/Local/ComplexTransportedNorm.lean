import OAI.RepresentationTheory.Weil.Local.ArchimedeanNorm

/-! # Complex Transported Norm -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexTransportedNorm.Construction

noncomputable section

/-! The transported complex norm is a positive power of the usual complex modulus. -/

theorem continuous_complex_embedding_circle_norm
    {k : Type} [NormedField k] (e : ℂ →+* k) (he : Continuous e) (u : Circle) :
    ‖e (u : ℂ)‖ = 1 := by
  have hcont : Continuous (fun v : Circle => ‖e (v : ℂ)‖) := (he.comp continuous_subtype_val).norm
  obtain ⟨B, hB⟩ := (isCompact_range hcont).bddAbove
  have hle (v : Circle) : ‖e (v : ℂ)‖ ≤ 1 := by
    by_contra! hv
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt B hv
    have hb := hB (Set.mem_range_self (v ^ m))
    simp only [Circle.coe_pow, map_pow, norm_pow] at hb
    exact not_lt_of_ge hb hm
  have hprod : ‖e (u : ℂ)‖ * ‖e ((u⁻¹ : Circle) : ℂ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, map_one, norm_one]
  apply le_antisymm (hle u)
  calc
    1 = ‖e (u : ℂ)‖ * ‖e ((u⁻¹ : Circle) : ℂ)‖ := hprod.symm
    _ ≤ ‖e (u : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left (hle u⁻¹) (norm_nonneg _)
    _ = ‖e (u : ℂ)‖ := mul_one _

theorem continuous_complex_embedding_norm_power
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) (e : ℂ →+* k) (he : Continuous e) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ z : ℂ, ‖e z‖ = ‖z‖ ^ s := by
  obtain ⟨s, hs, hs1, hR⟩ := ArchimedeanNorm.Construction.continuous_real_embedding_norm_power h (e.comp Complex.ofRealHom)
    (he.comp Complex.continuous_ofReal)
  refine ⟨s, hs, hs1, fun z => ?_⟩
  by_cases hz : z = 0
  · simp [hz, hs.ne']
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnC : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let u : Circle := ⟨z / (‖z‖ : ℂ), by
    change z / (‖z‖ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_self hn]⟩
  have hpolar : z = (‖z‖ : ℂ) * (u : ℂ) := by
    change z = (‖z‖ : ℂ) * (z / (‖z‖ : ℂ))
    field_simp
  calc
    ‖e z‖ = ‖e (‖z‖ : ℂ)‖ * ‖e (u : ℂ)‖ := by rw [← norm_mul, ← map_mul, ← hpolar]
    _ = ‖z‖ ^ s := by
      rw [continuous_complex_embedding_circle_norm e he u, mul_one]
      simpa only [RingHom.comp_apply, abs_of_nonneg (norm_nonneg _)] using! hR ‖z‖

end

end OAI.RepresentationTheory.Weil.Local.ComplexTransportedNorm.Construction
