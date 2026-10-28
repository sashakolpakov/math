import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds

/-! # Quadratic Lower -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.QuadraticLower

noncomputable section

section

/-! Uniform lower bounds for a continuous positive quadratic function on a compact parameter set. -/

open Set

variable {Z F : Type} [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]

theorem positive_quadratic_uniform_lower (Q : Z → F → ℝ) {K : Set Z}
    (hK : IsCompact K) (hQ : ContinuousOn (fun p : Z × F => Q p.1 p.2) (K ×ˢ Set.univ))
    (hzero : ∀ x ∈ K, Q x 0 = 0)
    (hscale : ∀ x ∈ K, ∀ r : ℝ, ∀ v : F, Q x (r • v) = r ^ 2 * Q x v)
    (hpos : ∀ x ∈ K, ∀ v : F, v ≠ 0 → 0 < Q x v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : F, c * ‖v‖ ^ 2 ≤ Q x v := by
  have hcompact := hK.prod (isCompact_sphere (0 : F) 1)
  obtain ⟨c, hc, hb⟩ := hcompact.exists_forall_le'
    (hQ.mono (fun _ hp => ⟨hp.1, Set.mem_univ _⟩)) (a := (0 : ℝ)) (by
      rintro ⟨x, v⟩ ⟨hx, hv⟩
      apply hpos x hx v
      intro hz
      have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn)
  refine ⟨c, hc, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · subst v
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, hzero x hx, le_refl]
  · let w := (‖v‖⁻¹ : ℝ) • v
    have hw : w ∈ Metric.sphere (0 : F) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      change ‖(‖v‖⁻¹ : ℝ) • v‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hn : ‖v‖ • w = v := by
      change ‖v‖ • ((‖v‖⁻¹ : ℝ) • v) = v
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    calc
      c * ‖v‖ ^ 2 ≤ Q x w * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right (hb (x, w) ⟨hx, hw⟩) (sq_nonneg _)
      _ = Q x (‖v‖ • w) := (mul_comm _ _).trans (hscale x hx ‖v‖ w).symm
      _ = Q x v := congrArg (Q x) hn

end

/-! Uniform upper bounds for continuous quadratic functions on compact parameter sets. -/

open Set

variable {Z F : Type} [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]

theorem quadratic_uniform_upper (Q : Z → F → ℝ) {K : Set Z}
    (hK : IsCompact K) (hQ : ContinuousOn (fun p : Z × F => Q p.1 p.2) (K ×ˢ Set.univ))
    (hzero : ∀ x ∈ K, Q x 0 = 0)
    (hscale : ∀ x ∈ K, ∀ r : ℝ, ∀ v : F, Q x (r • v) = r ^ 2 * Q x v) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ v : F, Q x v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨R, hR⟩ := (hK.prod (isCompact_sphere (0 : F) 1)).bddAbove_image
    (hQ.mono (fun _ hp => ⟨hp.1, Set.mem_univ _⟩))
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x hx v => ?_⟩
  by_cases hv : v = 0
  · subst v
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, hzero x hx, le_refl]
  · let w := (‖v‖⁻¹ : ℝ) • v
    have hw : w ∈ Metric.sphere (0 : F) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      change ‖(‖v‖⁻¹ : ℝ) • v‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
    have hn : ‖v‖ • w = v := by
      change ‖v‖ • ((‖v‖⁻¹ : ℝ) • v) = v
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    calc
      Q x v = ‖v‖ ^ 2 * Q x w := (congrArg (Q x) hn).symm.trans (hscale x hx ‖v‖ w)
      _ ≤ ‖v‖ ^ 2 * max R 1 := mul_le_mul_of_nonneg_left
        ((hR ⟨(x, w), ⟨hx, hw⟩, rfl⟩).trans (le_max_left _ _)) (sq_nonneg _)
      _ = _ := mul_comm _ _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.QuadraticLower
