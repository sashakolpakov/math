import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CutoffEquation
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Cutoff

/-! Quantitative Hölder bounds for localization; the coefficient seminorm shrinks under dilation. -/

noncomputable section
open Set Metric
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem cutoff_holder_product {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (χ : E → ℝ) (g : E → F) {α H K M : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχh : ∀ x y, |χ x - χ y| ≤ K * ‖x - y‖ ^ α)
    (hgh : ∀ x y, ‖g x - g y‖ ≤ H * ‖x - y‖ ^ α)
    (hgm : ∀ x, χ x ≠ 0 → ‖g x‖ ≤ M) :
    (∀ x, ‖χ x • g x‖ ≤ M) ∧
    (∀ x y, ‖χ x • g x - χ y • g y‖ ≤ (H + K * M) * ‖x - y‖ ^ α) := by
  have hone (x) : |χ x| ≤ 1 := by rw [abs_of_nonneg (hχ x).1]; exact (hχ x).2
  have hb (x y) (hx : χ x ≠ 0) :
      ‖χ x • g x - χ y • g y‖ ≤ (H + K * M) * ‖x - y‖ ^ α := by
    have he : χ x • g x - χ y • g y =
        χ y • (g x - g y) + (χ x - χ y) • g x := by
      simp only [smul_sub, sub_smul]
      abel
    rw [he]
    calc
      _ ≤ ‖χ y • (g x - g y)‖ + ‖(χ x - χ y) • g x‖ := norm_add_le _ _
      _ = |χ y| * ‖g x - g y‖ + |χ x - χ y| * ‖g x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (H * ‖x - y‖ ^ α) + (K * ‖x - y‖ ^ α) * M := by
        apply add_le_add
        · exact mul_le_mul (hone y) (hgh x y) (norm_nonneg _) (by norm_num)
        · exact mul_le_mul (hχh x y) (hgm x hx) (norm_nonneg _)
            (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))
      _ = _ := by ring
  constructor
  · intro x
    by_cases hx : χ x = 0
    · simpa only [hx, zero_smul, norm_zero] using hM
    · rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hone x) (hgm x hx) (norm_nonneg _) (by norm_num)).trans_eq (one_mul M)
  · intro x y
    by_cases hx : χ x = 0
    · by_cases hy : χ y = 0
      · simp only [hx, hy, zero_smul, sub_self, norm_zero]
        positivity
      · simpa only [norm_sub_rev] using hb y x hy
    · exact hb x y hx

def dilatedDifference {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] (f : E → F) (x₀ : E) (r : ℝ) (x : E) : F :=
  f x₀ - f (x₀ + r • x)

theorem dilatedDifference_holder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α r : ℝ}
    (hr : 0 ≤ r) (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ x y : E) :
    ‖dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r x - dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r y‖ ≤
      (‖f‖ * r ^ α) * ‖x - y‖ ^ α := by
  have he : x₀ + r • x - (x₀ + r • y) = r • (x - y) := by
    rw [smul_sub]
    abel
  have h := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (x₀ + r • x) (x₀ + r • y)
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr,
    Real.mul_rpow hr (norm_nonneg _)] at h
  have he' : dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r x -
      dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r y =
      -(OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + r • x) - OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x₀ + r • y)) := by
    unfold dilatedDifference
    abel
  rw [he', norm_neg]
  exact h.trans_eq (by ring)

theorem dilatedDifference_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α r : ℝ}
    (hr : 0 ≤ r) (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ x : E) :
    ‖dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r x‖ ≤ (‖f‖ * r ^ α) * ‖x‖ ^ α := by
  simpa only [dilatedDifference, smul_zero, add_zero, sub_self, sub_zero] using
    dilatedDifference_holder hr f x₀ x 0

theorem exists_localized_difference_holder
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (x₀ : E) (r : ℝ), 0 ≤ r →
      ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = radialCutoff 1 x •
          dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r x) ∧
        ‖B‖ ≤ C * ‖f‖ * r ^ α ∧
        (∀ x, x ∉ closedBall 0 2 → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0) := by
  obtain ⟨K, hK, hχsup, hχholder⟩ := compact_C1_holder (radialCutoff (E := E) 1)
    ((contDiff_radialCutoff 1).of_le (by simp))
    (hasCompactSupport_radialCutoff zero_lt_one) hα hα1
  let C := (1 + K) * (1 + (2 : ℝ) ^ α)
  have hp : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₁ : (2 : ℝ) ^ α ≤ C := by dsimp [C]; nlinarith
  have hC₂ : 1 + K * (2 : ℝ) ^ α ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro f x₀ r hr
  let H := ‖f‖ * r ^ α
  have hH : 0 ≤ H := mul_nonneg (norm_nonneg f) (Real.rpow_nonneg hr _)
  let g := dilatedDifference (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) x₀ r
  have hgm : ∀ x, radialCutoff 1 x ≠ 0 → ‖g x‖ ≤ H * (2 : ℝ) ^ α := by
    intro x hx
    have hx2 : ‖x‖ ≤ 2 := by
      by_contra hh
      exact hx (radialCutoff_zero zero_lt_one (by linarith [lt_of_not_ge hh]))
    exact (dilatedDifference_bound hr f x₀ x).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hx2 hα) hH)
  have hprod := cutoff_holder_product (radialCutoff (E := E) 1) g hH hK.le
    (mul_nonneg hH hp.le) (fun x => ⟨radialCutoff_nonneg 1 x, radialCutoff_le_one 1 x⟩)
    (by simpa only [Real.norm_eq_abs] using hχholder)
    (dilatedDifference_holder hr f x₀) hgm
  have hsup : ∀ x, ‖radialCutoff 1 x • g x‖ ≤ C * H := by
    intro x
    exact (hprod.1 x).trans (by nlinarith [mul_le_mul_of_nonneg_right hC₁ hH])
  have hholder : ∀ x y, ‖radialCutoff 1 x • g x - radialCutoff 1 y • g y‖ ≤
      (C * H) * (dist x y) ^ α := by
    intro x y
    rw [dist_eq_norm]
    apply (hprod.2 x y).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
    nlinarith [mul_le_mul_of_nonneg_right hC₂ hH]
  have hg : Continuous g := by
    exact continuous_const.sub (f.val.1.continuous.comp
      (continuous_const.add (continuous_const.smul continuous_id)))
  let b : E →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => radialCutoff 1 x • g x) ((contDiff_radialCutoff 1).continuous.smul hg) (C * H) hsup
  let B : OAI.Analysis.Normed.Function.Holder.HolderMap E F α := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα b hholder
  refine ⟨B, (fun x => rfl), ?_, ?_⟩
  · have hb : ‖b‖ ≤ C * H :=
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (mul_nonneg hC.le hH) hsup
    calc
      ‖B‖ ≤ max ‖b‖ (C * H) := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα b (mul_nonneg hC.le hH) hholder
      _ ≤ C * H := max_le hb le_rfl
      _ = _ := by dsimp [H]; ring
  · intro x hx
    change radialCutoff 1 x • g x = 0
    have hx2 : 2 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    rw [radialCutoff_zero zero_lt_one (by linarith), zero_smul]

end OAI.Analysis.PDE.Schauder
