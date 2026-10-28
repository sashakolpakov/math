import OAI.Analysis.Calculus.Current.NormBounds

/-! The source's lateral boundary is separated from all small-cap velocities. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open scoped Matrix Matrix.Norms.Elementwise

theorem fiberDefining_normalized {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    fiberDefining w a z = (∑ i, ‖ratio z i‖ ^ 2) / w ^ 2 +
      100 * ‖phi z / (a : ℂ)‖ ^ 2 - 1 := by
  rw [fiberDefining_formula]
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  ring

theorem phaseCutoff_ne_zero_norm_lt (q : ℂ) (hq : phaseCutoff q ≠ 0) :
    ‖q‖ < 1 / 20 := by
  by_contra hn
  exact hq (phaseCutoff_eq_zero q (le_of_not_gt hn))

theorem fiber_lateral_ratio_lower {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z = 0)
    (hg : phaseCutoff (phi z / (a : ℂ)) ≠ 0) :
    (1 : ℝ) / 400 ≤ ∑ i, ‖ratio z i‖ ^ 2 := by
  rw [fiberDefining_normalized] at hr
  have hq := phaseCutoff_ne_zero_norm_lt _ hg
  have hqs : ‖phi z / (a : ℂ)‖ ^ 2 ≤ (1 / 20 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hq.le 2
  norm_num at hr hqs
  nlinarith

theorem ratio_sq_le_distance_velocity {d : ℕ} (W : Fin d → ℂ) (v : Fin d → ℝ) :
    (∑ i, ‖W i‖ ^ 2) ≤ 2 * squaredDistance W v + 2 * ∑ i, |v i| ^ 2 := by
  have hi (i : Fin d) : ‖W i‖ ^ 2 ≤ 2 * ‖W i - (v i : ℂ)‖ ^ 2 + 2 * |v i| ^ 2 := by
    have hn : ‖W i‖ ≤ ‖W i - (v i : ℂ)‖ + |v i| := by
      calc
        ‖W i‖ = ‖(W i - (v i : ℂ)) + (v i : ℂ)‖ := by congr 1; ring
        _ ≤ ‖W i - (v i : ℂ)‖ + ‖(v i : ℂ)‖ := norm_add_le _ _
        _ = _ := by simp
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖W i - (v i : ℂ)‖ - |v i|)]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simpa only [squaredDistance, Finset.sum_add_distrib, ← Finset.mul_sum] using hh

theorem lateral_squaredDistance_lower {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (hr : fiberDefining (1 / 10) a z = 0)
    (hg : phaseCutoff (phi z / (a : ℂ)) ≠ 0) (v : Fin d → ℝ)
    (hv : (∑ i, |v i| ^ 2) ≤ 1 / 1600) :
    (1 : ℝ) / 1600 ≤ squaredDistance (ratio z) v := by
  have hw := fiber_lateral_ratio_lower a z hr hg
  have hd := ratio_sq_le_distance_velocity (ratio z) v
  linarith

theorem normalizedModeAmplitude_lateral_norm_le {d : ℕ}
    (a κ cR cI : ℝ) (hκ : 0 < κ) (v : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (hr : fiberDefining (1 / 10) a z = 0)
    (hg : phaseCutoff (phi z / (a : ℂ)) ≠ 0)
    (hv : (∑ i, |v i| ^ 2) ≤ 1 / 1600) :
    ‖normalizedModeAmplitude κ cR cI v x z‖ ≤
      ((κ / ‖z none‖) ^ ((d : ℝ) / 2) *
        Real.exp (-κ * ‖z none‖ / 3200)) * ‖(⟨cR, cI⟩ : ℂ)‖ := by
  rw [normalizedModeAmplitude_norm κ cR cI hκ v x z hY]
  have hd := lateral_squaredDistance_lower a z hr hg v hv
  have hmul := mul_le_mul_of_nonneg_left hd (show 0 ≤ κ * ‖z none‖ / 2 by positivity)
  have he : Real.exp (-κ * ‖z none‖ / 2 * squaredDistance (ratio z) v) ≤
      Real.exp (-κ * ‖z none‖ / 3200) := Real.exp_le_exp.mpr (by nlinarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (norm_nonneg _)

end OAI.Analysis.Calculus.Current
