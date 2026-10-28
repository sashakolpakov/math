import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Affine
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.LocalBootstrap

/-! Small supported coefficient fields obtained by actual freezing and dilation. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem exists_small_positive_rpow_mul {α K ε ρ : ℝ}
    (hα : 0 < α) (hK : 0 ≤ K) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ r > 0, r < ρ ∧ K * r ^ α < ε := by
  obtain ⟨t, ht, hKt⟩ := exists_pos_mul_lt hε K
  let r := min ρ (t ^ α⁻¹) / 2
  have hroot : 0 < t ^ α⁻¹ := Real.rpow_pos_of_pos ht _
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : r < ρ := by dsimp [r]; linarith [min_le_left ρ (t ^ α⁻¹)]
  have hrt : r < t ^ α⁻¹ := by dsimp [r]; linarith [min_le_right ρ (t ^ α⁻¹)]
  have hrpow : r ^ α < t := by
    have hh := Real.rpow_lt_rpow hr.le hrt hα
    rw [Real.rpow_inv_rpow ht.le hα.ne'] at hh
    exact hh
  exact ⟨r, hr, hrρ, lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrpow.le hK) (by nlinarith)⟩

theorem exists_small_localized_difference
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hρ : 0 < ρ)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ : E) :
    ∃ r > 0, r < ρ ∧ ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = radialCutoff 1 x •
        dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r x) ∧
      ‖B‖ < ε ∧ (∀ x, x ∉ closedBall 0 2 → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0) := by
  obtain ⟨C, hC, hb⟩ := exists_localized_difference_holder (E := E) (F := F) hα.le hα1.le
  obtain ⟨r, hr, hrρ, hsmall⟩ := exists_small_positive_rpow_mul hα
    (mul_nonneg hC.le (norm_nonneg f)) hε hρ
  obtain ⟨B, hval, hnorm, hs⟩ := hb f x₀ r hr.le
  exact ⟨r, hr, hrρ, B, hval, hnorm.trans_lt (by nlinarith [hsmall]), hs⟩

theorem posDef_identity_cutoff {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hA : t ≠ 0 → A.PosDef) :
    (1 - t • (1 - A)).PosDef := by
  have hI : (1 : Matrix (Fin m) (Fin m) ℝ).PosDef := Matrix.PosDef.one
  by_cases ht0 : t = 0
  · simpa [ht0] using hI
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hsum := Matrix.PosDef.posSemidef_add
    (hI.posSemidef.smul (show 0 ≤ 1 - t by linarith)) ((hA ht0).smul htpos)
  have he : (1 - t) • (1 : Matrix (Fin m) (Fin m) ℝ) + t • A = 1 - t • (1 - A) := by
    simp only [sub_smul, smul_sub, one_smul]
    abel
  rwa [he] at hsum

end OAI.Analysis.PDE.Schauder
