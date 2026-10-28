import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds

/-! # Metric Domination -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.MetricDomination

noncomputable section

/-! Actual continuous curvature coefficients are dominated by a sufficiently large integral positive metric. -/

open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {Z : Type} [TopologicalSpace Z]

theorem compact_bilinear_positive_after_nat_multiple
    (B Q : Z → E →L[ℝ] E →L[ℝ] ℝ) {K : Set Z} (hK : IsCompact K)
    (hB : ContinuousOn B K) (hQ : ContinuousOn Q K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < Q x v v) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m → ∀ x ∈ K, ∀ v : E, v ≠ 0 →
      0 < B x v v + (m : ℝ) * Q x v v := by
  obtain ⟨c, hc, hlow⟩ := ComplexMultiplication.HodgeComparison.MetricBounds.CM.Construction.positive_bilinear_uniform_lower_bound Q hK hQ hpos
  obtain ⟨C, hC, hupp⟩ := ComplexMultiplication.HodgeComparison.MetricBounds.CM.Construction.bilinear_uniform_upper_bound B hK hB
  obtain ⟨N, hN⟩ := exists_nat_gt (C / c)
  have hNpos : 0 < N := by exact_mod_cast (lt_trans (div_pos hC hc) hN)
  refine ⟨N, hNpos, ?_⟩
  intro m hm x hx v hv
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hCm : C < (m : ℝ) * c :=
    ((div_lt_iff₀ hc).mp hN).trans_le (mul_le_mul_of_nonneg_right hNm hc.le)
  have hq := mul_le_mul_of_nonneg_left (hlow x hx v) (Nat.cast_nonneg (α := ℝ) m)
  have hb := (abs_le.mp (hupp x hx v v)).1
  have hstrict : 0 < ((m : ℝ) * c - C) * (‖v‖ * ‖v‖) :=
    mul_pos (sub_pos.mpr hCm) (mul_pos (norm_pos_iff.mpr hv) (norm_pos_iff.mpr hv))
  nlinarith

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.MetricDomination
