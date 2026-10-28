import OAI.Analysis.PDE.Nonlinear.LocalHolder

/-! Hölder localization for a vector-valued field. -/

noncomputable section
open Set Metric
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

theorem exists_cutoff_holder_field
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : E → ℝ) (g : E → F) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hg : Continuous g) (x₀ : E) {r R α C : ℝ}
    (hrR : r < R) (hR : 0 ≤ R) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hs : ∀ x, x ∉ closedBall x₀ r → χ x = 0)
    (hh : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      ‖g x - g y‖ ≤ C * ‖x - y‖ ^ α) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap E F α, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = χ x • g x := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ (mem_closedBall_self hR))
  obtain ⟨K, hK, _, hKh⟩ := OAI.Analysis.PDE.Schauder.compact_C1_holder χ hχ hχc hα hα1
  have hprod : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      ‖χ x • g x - χ y • g y‖ ≤ (C + K * M) * ‖x - y‖ ^ α := by
    intro x hx y hy
    have he : χ x • g x - χ y • g y = χ y • (g x - g y) + (χ x - χ y) • g x := by
      simp only [smul_sub, sub_smul]
      abel
    rw [he]
    calc
      _ ≤ ‖χ y • (g x - g y)‖ + ‖(χ x - χ y) • g x‖ := norm_add_le _ _
      _ = |χ y| * ‖g x - g y‖ + |χ x - χ y| * ‖g x‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (C * ‖x - y‖ ^ α) + (K * ‖x - y‖ ^ α) * M := by
        apply add_le_add
        · apply mul_le_mul _ (hh x hx y hy) (norm_nonneg _) (by norm_num)
          rw [abs_of_nonneg (hχ01 y).1]
          exact (hχ01 y).2
        · exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hKh x y) (hM x hx)
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact exists_holder_of_support_separated (fun x => χ x • g x) (hχ.continuous.smul hg)
    hχc.smul_right x₀ hrR hα (by positivity) (by intro x hx; rw [hs x hx, zero_smul]) hprod

end OAI.Analysis.PDE.Nonlinear
