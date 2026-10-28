import OAI.Analysis.PDE.Concentration.ParameterStability

noncomputable section
namespace OAI.Analysis.PDE.Concentration

theorem output_log_threshold (d : ℕ) {δ C D : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < D) :
    ∃ L₀ : ℝ, 10000 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      0 < L ∧ (Real.sqrt L)⁻¹ ≤ 1 / 100 ∧ D ≤ L * δ ∧
        C * D / L ≤ (Real.sqrt L)⁻¹ / (4 * ((d : ℝ) + 1)) := by
  let Q := 4 * ((d : ℝ) + 1) * C * D
  let L₀ := max 10000 (max (D / δ) (Q ^ 2))
  refine ⟨L₀, le_max_left _ _, ?_⟩
  intro L hL
  have hLbig : 10000 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hLd : D / δ ≤ L := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hL
  have hLQ : Q ^ 2 ≤ L := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hL
  have hs : 100 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) hL0.le]
    norm_num
    exact hLbig
  have hgamma : (Real.sqrt L)⁻¹ ≤ (1 / 100 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) hs
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hQsqrt : Q ≤ Real.sqrt L := (Real.le_sqrt hQ hL0.le).mpr hLQ
  refine ⟨hL0, hgamma, (div_le_iff₀ hδ).mp hLd, ?_⟩
  have hn : 0 < 4 * ((d : ℝ) + 1) := by positivity
  have hsq := mul_le_mul_of_nonneg_right hQsqrt (Real.sqrt_nonneg L)
  rw [Real.mul_self_sqrt hL0.le] at hsq
  rw [show (Real.sqrt L)⁻¹ / (4 * ((d : ℝ) + 1)) =
      1 / (Real.sqrt L * (4 * ((d : ℝ) + 1))) by field_simp]
  apply (div_le_div_iff₀ hL0 (mul_pos (Real.sqrt_pos.mpr hL0) hn)).mpr
  dsimp only [Q] at hsq
  nlinarith

end OAI.Analysis.PDE.Concentration
