import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Freeze

/-! A common coefficient-freezing radius for an entire bounded Hölder family. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem exists_uniform_small_localized_difference
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α N ε ρ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hN : 0 ≤ N)
    (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ r > 0, r < ρ ∧ ∀ (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α), ‖f‖ ≤ N → ∀ x₀ : E,
      ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = radialCutoff 1 x •
          dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r x) ∧
        ‖B‖ < ε ∧ (∀ x, x ∉ closedBall 0 2 → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0) := by
  obtain ⟨C, hC, hb⟩ := exists_localized_difference_holder (E := E) (F := F) hα.le hα1.le
  obtain ⟨r, hr, hrρ, hsmall⟩ := exists_small_positive_rpow_mul hα
    (mul_nonneg hC.le hN) hε hρ
  refine ⟨r, hr, hrρ, ?_⟩
  intro f hf x₀
  obtain ⟨B, hval, hn, hs⟩ := hb f x₀ r hr.le
  refine ⟨B, hval, hn.trans_lt ?_, hs⟩
  have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hC.le)
    (Real.rpow_nonneg hr.le α)
  exact hbound.trans_lt (by simpa only [mul_assoc] using hsmall)

theorem exists_uniform_halfspace_freezing {m : ℕ} {α N ε ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hN : 0 ≤ N) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ r > 0, r < ρ ∧
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
        ‖A‖ ≤ N → OAI.Analysis.Normed.Function.Holder.HolderMap.value A 0 = 1 →
        ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
          ‖B‖ < ε ∧
          (∀ x, ‖x‖ ≤ 1 → 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = OAI.Analysis.Normed.Function.Holder.HolderMap.value A (r • x)) ∧
          (∀ x, x ∉ closedBall 0 2 → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0) := by
  obtain ⟨r, hr, hrρ, hB⟩ := exists_uniform_small_localized_difference
    (E := EuclideanSpace ℝ (Fin m)) (F := Matrix (Fin m) (Fin m) ℝ) hα hα1 hN hε hρ
  refine ⟨r, hr, hrρ, ?_⟩
  intro A hA hA0
  obtain ⟨B, hval, hn, hs⟩ := hB A hA 0
  refine ⟨B, hn, ?_, hs⟩
  intro x hx
  rw [hval, radialCutoff_one zero_lt_one hx, one_smul]
  simp only [dilatedDifference, hA0, zero_add, sub_sub_cancel]

end OAI.Analysis.PDE.Schauder
