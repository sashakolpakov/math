import Mathlib

/-! Positivity propagation for the scalar differential equation used by the
Moore determinant on a positive matrix segment. -/

namespace OAI.LinearAlgebra.Moore

open Set

theorem positive_of_scalar_linear_ode {f c : ℝ → ℝ}
    (hc : ContinuousOn c (Icc 0 1))
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (c t * f t) t)
    (h0 : 0 < f 0) : 0 < f 1 := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0 := by
    intro t ht hz
    let g : ℝ → ℝ := fun s ↦ f (t - s)
    have hmem : ∀ s ∈ Icc 0 t, t - s ∈ Icc (0 : ℝ) 1 := by
      intro s hs
      constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
    have hg : ContinuousOn g (Icc 0 t) :=
      hfc.comp (continuous_const.sub continuous_id).continuousOn hmem
    have hg' : ∀ s ∈ Ico 0 t,
        HasDerivWithinAt g (-(c (t - s) * f (t - s))) (Ici s) s := by
      intro s hs
      have hd := (hf (t - s) (hmem s ⟨hs.1, hs.2.le⟩)).comp s
        ((hasDerivAt_const s t).sub (hasDerivAt_id s))
      convert! hd.hasDerivWithinAt using 1
      simp
    have hb : ∀ s ∈ Ico 0 t, ‖-(c (t - s) * f (t - s))‖ ≤ C * ‖g s‖ := by
      intro s hs
      simpa only [norm_neg, norm_mul, g] using
        mul_le_mul_of_nonneg_right (hC (t - s) (hmem s ⟨hs.1, hs.2.le⟩))
          (norm_nonneg (f (t - s)))
    have hzall := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hg hg'
      (show g 0 = 0 by simpa [g] using hz) hb
    have hz0 := hzall t ⟨ht.1, le_rfl⟩
    simp only [g, sub_self] at hz0
    linarith
  by_contra hn
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1) hfc
    (show 0 ∈ Icc (f 1) (f 0) from ⟨le_of_not_gt hn, h0.le⟩)
  exact hne t ht hft

end OAI.LinearAlgebra.Moore
