import OAI.Analysis.PDE.Concentration.LocalSupermean
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
open scoped ContDiff Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem halfBall_integral_le_weighted {f : E → ℝ} (hf : Continuous f)
    (x : E) {r c : ℝ} (hr : 0 ≤ r)
    (hc : ∀ y ∈ closedBall (0 : E) (1 / 2), c ≤ meanWeight y)
    (hn : ∀ y ∈ closedBall x r, 0 ≤ f y) :
    c * (∫ y in closedBall (0 : E) (1 / 2), f (x + r • y)) ≤
      weightedBallAverage f x r := by
  have hcont : Continuous (fun y : E => f (x + r • y)) :=
    hf.comp (continuous_const.add (continuous_id.const_smul r))
  have hi := hcont.continuousOn.integrableOn_compact (μ := volume)
    (isCompact_closedBall (0 : E) (1 / 2))
  have hwi : Integrable (fun y : E => meanWeight y * f (x + r • y)) :=
    (contDiff_meanWeight.continuous.mul hcont).integrable_of_hasCompactSupport
      hasCompactSupport_meanWeight.mul_right
  have hnonneg {y : E} (hy : ‖y‖ ≤ 1) : 0 ≤ f (x + r • y) := by
    apply hn
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr hy
  rw [← integral_const_mul, ← integral_indicator measurableSet_closedBall]
  apply integral_mono ((integrable_indicator_iff measurableSet_closedBall).mpr (hi.const_mul c)) hwi
  intro y
  dsimp only
  by_cases hy : y ∈ closedBall (0 : E) (1 / 2)
  · rw [indicator_of_mem hy]
    apply mul_le_mul_of_nonneg_right (hc y hy)
    apply hnonneg
    have h : ‖y‖ ≤ 1 / 2 := by simpa using hy
    linarith
  · rw [indicator_of_notMem hy]
    by_cases hy1 : ‖y‖ ≤ 1
    · exact mul_nonneg (meanWeight_nonneg y) (hnonneg hy1)
    · rw [meanWeight_zero (lt_of_not_ge hy1), zero_mul]

theorem exists_uniform_halfBall_mean_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (f : E → ℝ), ContDiff ℝ 2 f → ∀ (x : E) (r : ℝ), 0 ≤ r →
      (∀ y ∈ closedBall x r, 0 ≤ f y) → (∀ y ∈ closedBall x r, Δ f y ≤ 0) →
      (∫ y in closedBall (0 : E) (1 / 2), f (x + r • y)) ≤ C * f x := by
  obtain ⟨c, hc, hminor⟩ := meanWeight_lower_on_half_ball (E := E)
  let C : ℝ := (∫ y : E, meanWeight y) / c + 1
  have hm : 0 ≤ ∫ y : E, meanWeight y := integral_nonneg meanWeight_nonneg
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro f hf x r hr hn hΔ
  have h1 := halfBall_integral_le_weighted hf.continuous x hr hminor hn
  have h2 := weightedBallAverage_le hf x hr hΔ
  have hfx := hn x (mem_closedBall_self hr)
  have h3 : (∫ y in closedBall (0 : E) (1 / 2), f (x + r • y)) ≤
      ((∫ y : E, meanWeight y) / c) * f x := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [h1.trans h2]
  dsimp [C]
  nlinarith

theorem halfBall_affine_integral (f : E → ℝ) (x : E) {r : ℝ} (hr : 0 < r) :
    (∫ y in closedBall (0 : E) (1 / 2), f (x + r • y)) =
      (r ^ Module.finrank ℝ E)⁻¹ * ∫ y in closedBall x (r / 2), f y := by
  classical
  let g : E → ℝ := (closedBall x (r / 2)).indicator f
  have he (y : E) : (closedBall (0 : E) (1 / 2)).indicator
      (fun y => f (x + r • y)) y = g (x + r • y) := by
    have hm : x + r • y ∈ closedBall x (r / 2) ↔ y ∈ closedBall (0 : E) (1 / 2) := by
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr]
      rw [div_eq_mul_inv r 2]
      simpa using (mul_le_mul_iff_right₀ hr : r * ‖y‖ ≤ r * (1 / 2) ↔ ‖y‖ ≤ 1 / 2)
    by_cases hy : y ∈ closedBall (0 : E) (1 / 2)
    · simp only [indicator_of_mem hy, g, indicator_of_mem (hm.mpr hy)]
    · simp only [indicator_of_notMem hy, g, indicator_of_notMem (mt hm.mp hy)]
  rw [← integral_indicator measurableSet_closedBall]
  simp_rw [he]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun z => g (x + z)) r (hR := hr.le),
    integral_add_left_eq_self g x]
  rw [integral_indicator measurableSet_closedBall]
  rfl

theorem exists_uniform_ball_mean_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (f : E → ℝ), ContDiff ℝ 2 f → ∀ (x : E) (r : ℝ), 0 < r →
      (∀ y ∈ closedBall x r, 0 ≤ f y) → (∀ y ∈ closedBall x r, Δ f y ≤ 0) →
      (∫ y in closedBall x (r / 2), f y) ≤ C * r ^ Module.finrank ℝ E * f x := by
  obtain ⟨C, hC, hmean⟩ := exists_uniform_halfBall_mean_constant (E := E)
  refine ⟨C, hC, ?_⟩
  intro f hf x r hr hn hΔ
  have h := hmean f hf x r hr.le hn hΔ
  rw [halfBall_affine_integral f x hr] at h
  have hp : 0 < r ^ Module.finrank ℝ E := pow_pos hr _
  have h' := (mul_le_mul_iff_right₀ hp).mpr h
  simpa only [mul_inv_cancel_left₀ hp.ne', mul_left_comm, mul_assoc] using h'

end OAI.Analysis.PDE.Concentration
