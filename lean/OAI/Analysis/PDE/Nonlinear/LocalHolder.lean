import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CutoffHolder

/-! Extension by zero of a Hölder field whose support is strictly inside a ball. -/

noncomputable section
open Set Metric
open scoped Topology
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

theorem holder_of_support_separated
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (x₀ : E) {r R α C M : ℝ}
    (hrR : r < R) (hα : 0 ≤ α) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hs : ∀ x, x ∉ closedBall x₀ r → f x = 0)
    (hb : ∀ x, ‖f x‖ ≤ M)
    (hh : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) :
    ∀ x y, ‖f x - f y‖ ≤ (C + 2 * M / (R - r) ^ α) * ‖x - y‖ ^ α := by
  have hgap : 0 < (R - r) ^ α := Real.rpow_pos_of_pos (sub_pos.mpr hrR) _
  have hcoef : 0 ≤ C + 2 * M / (R - r) ^ α := by positivity
  have hout (x y : E) (hx : x ∉ closedBall x₀ R) :
      ‖f x - f y‖ ≤ (C + 2 * M / (R - r) ^ α) * ‖x - y‖ ^ α := by
    have hxr : x ∉ closedBall x₀ r := fun h => hx (closedBall_subset_closedBall hrR.le h)
    rw [hs x hxr]
    by_cases hy : y ∈ closedBall x₀ r
    · have hd : R - r ≤ ‖x - y‖ := by
        have hx' : R < dist x x₀ := lt_of_not_ge hx
        have ht := dist_triangle x y x₀
        have hy' : dist y x₀ ≤ r := hy
        rw [dist_eq_norm x y] at ht
        linarith only [hx', ht, hy']
      have hp := Real.rpow_le_rpow (sub_nonneg.mpr hrR.le) hd hα
      have hratio : 2 * M ≤ (2 * M / (R - r) ^ α) * ‖x - y‖ ^ α := by
        calc
          _ = (2 * M / (R - r) ^ α) * (R - r) ^ α := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
      simp only [zero_sub, norm_neg]
      calc
        ‖f y‖ ≤ M := hb y
        _ ≤ 2 * M := by linarith only [hM]
        _ ≤ (2 * M / (R - r) ^ α) * ‖x - y‖ ^ α := hratio
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hC])
          (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [hs y hy, sub_zero, norm_zero]
      positivity
  intro x y
  by_cases hx : x ∈ closedBall x₀ R
  · by_cases hy : y ∈ closedBall x₀ R
    · exact (hh x hx y hy).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
        (Real.rpow_nonneg (norm_nonneg _) _))
    · simpa only [norm_sub_rev] using hout y x hy
  · exact hout x y hx

theorem exists_holder_of_support_separated
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : Continuous f) (hfc : HasCompactSupport f) (x₀ : E)
    {r R α C : ℝ} (hrR : r < R) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hs : ∀ x, x ∉ closedBall x₀ r → f x = 0)
    (hh : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap E F α, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = f x := by
  obtain ⟨M, hb⟩ := hfc.exists_bound_of_continuous hf
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hb 0)
  let b := BoundedContinuousFunction.ofNormedAddCommGroup f hf M hb
  have hh' : ∀ x y, ‖b x - b y‖ ≤ (C + 2 * M / (R - r) ^ α) * dist x y ^ α := by
    intro x y
    change ‖f x - f y‖ ≤ _
    simpa only [dist_eq_norm] using holder_of_support_separated f x₀ hrR hα hC hM hs hb hh x y
  exact ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα b hh', fun _ => rfl⟩

end OAI.Analysis.PDE.Nonlinear
