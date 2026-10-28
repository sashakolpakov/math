import Mathlib

/-! # Proper Quadratic -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ProperQuadratic.Construction

noncomputable section

/-! A continuous anisotropic homogeneous quadratic map on a proper normed
space is proper. The argument uses a compact annulus and scalar rescaling. -/

open _root_.Metric _root_.Topology

variable {F V : Type} [NontriviallyNormedField F]
variable [NormedAddCommGroup V] [NormedSpace F V] [ProperSpace V] [Nontrivial V]
variable (q : V → F) (hc : Continuous q)
variable (hhom : ∀ a : F, ∀ x : V, q (a • x) = a ^ 2 * q x)
variable (hzero : ∀ x, q x = 0 → x = 0)

include hc hhom hzero in
theorem anisotropic_quadratic_lower_bound : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ^ 2 ≤ ‖q x‖ := by
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm F
  let K : Set V := closedBall 0 1 ∩ {x | 1 / ‖a‖ ≤ ‖x‖}
  have hK : IsCompact K := (isCompact_closedBall (0 : V) 1).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨b, _, hb, hb', _⟩ := rescale_to_shell ha zero_lt_one hx
    exact ⟨b • x, by simpa only [K, Set.mem_inter_iff, mem_closedBall, dist_zero_right,
      Set.mem_ofPred_eq] using And.intro hb.le hb'⟩
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne hc.norm.continuousOn
  have hyne : y ≠ 0 := by
    intro hz
    have hh : 1 / ‖a‖ ≤ ‖y‖ := hy.2
    rw [hz, norm_zero] at hh
    exact (div_pos zero_lt_one (lt_trans zero_lt_one ha)).not_ge hh
  have hpos : 0 < ‖q y‖ := norm_pos_iff.mpr (fun hz => hyne (hzero y hz))
  refine ⟨‖q y‖, hpos, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨b, _, hb, hb', _⟩ := rescale_to_shell ha zero_lt_one hx
  have hbx : b • x ∈ K := by
    exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hb.le, hb'⟩
  have hlow : ‖q y‖ ≤ ‖b‖ ^ 2 * ‖q x‖ := by
    have hh : ‖q y‖ ≤ ‖q (b • x)‖ := hmin hbx
    simpa only [hhom, norm_mul, norm_pow] using hh
  have hscale : ‖b‖ ^ 2 * ‖x‖ ^ 2 ≤ 1 := by
    have hh : ‖b‖ * ‖x‖ ≤ 1 := by simpa only [norm_smul] using hb.le
    have hs := pow_le_pow_left₀ (mul_nonneg (norm_nonneg b) (norm_nonneg x)) hh 2
    simpa only [mul_pow, one_pow] using hs
  calc
    ‖q y‖ * ‖x‖ ^ 2 ≤ (‖b‖ ^ 2 * ‖q x‖) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlow (sq_nonneg ‖x‖)
    _ = (‖b‖ ^ 2 * ‖x‖ ^ 2) * ‖q x‖ := by ring
    _ ≤ 1 * ‖q x‖ := mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ = ‖q x‖ := one_mul _

include hc hhom hzero in
theorem anisotropic_quadratic_isProperMap : IsProperMap q := by
  obtain ⟨c, hcpos, hbound⟩ := anisotropic_quadratic_lower_bound q hc hhom hzero
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hc, fun K hK => ?_⟩
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  have hsub : q ⁻¹' K ⊆ closedBall 0 (R / c + 1) := by
    intro x hx
    have hsq : ‖x‖ ^ 2 ≤ R / c := by
      apply (le_div_iff₀ hcpos).mpr
      exact (mul_comm _ _).le.trans ((hbound x).trans (hR (q x) hx))
    rw [mem_closedBall, dist_zero_right]
    nlinarith [sq_nonneg (‖x‖ - 1 / 2)]
  exact (isCompact_closedBall (0 : V) (R / c + 1)).of_isClosed_subset
    (hK.isClosed.preimage hc) hsub

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ProperQuadratic.Construction
