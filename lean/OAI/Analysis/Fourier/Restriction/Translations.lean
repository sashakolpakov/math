import OAI.Analysis.Fourier.Restriction.FourierAmplitude
import OAI.Analysis.Fourier.Restriction.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem angularFourier_translate {n : ℕ} (f : Space n → ℂ) (z ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (x - z)) ξ =
      Complex.exp (-Complex.I * ((inner ℝ z ξ : ℝ) : ℂ)) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  rw [← integral_add_right_eq_self (fun x : Space n ↦
    Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * f (x - z)) z]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [add_sub_cancel_right, inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem angularFourier_indicator_ball {n : ℕ} (r : ℝ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier ((ball (0 : Space n) r).indicator (fun _ ↦ (1 : ℂ))) ξ =
      ∫ x in ball (0 : Space n) r, Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier
  have he : (fun x : Space n ↦ Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) *
      (ball (0 : Space n) r).indicator (fun _ ↦ (1 : ℂ)) x) =
      (ball (0 : Space n) r).indicator (fun x ↦ Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ))) := by
    funext x
    by_cases hx : x ∈ ball (0 : Space n) r <;> simp [hx]
  rw [he, integral_indicator measurableSet_ball]

/-- A fixed small ball has a Fourier transform bounded away from zero on
the unit sphere, providing the nonvanishing bump for discretization. -/
theorem small_ball_fourier_lower {n : ℕ} {r : ℝ} (hr : r ≤ 1 / 4)
    {ξ : Space n} (hξ : ‖ξ‖ ≤ 1) :
    volume.real (ball (0 : Space n) r) / 2 ≤
      ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier ((ball (0 : Space n) r).indicator (fun _ ↦ (1 : ℂ))) ξ‖ := by
  let μ := (volume : Measure (Space n)).restrict (ball 0 r)
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (ball (0 : Space n) r) < ⊤)⟩
  have hm : Measurable (fun x : Space n ↦ -(inner ℝ x ξ)) := by fun_prop
  have hs : ∀ᵐ x ∂μ, |-(inner ℝ x ξ)| ≤ 1 / 4 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hx' : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using hx
    rw [abs_neg]
    calc
      _ ≤ ‖x‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left hξ (norm_nonneg _)
      _ ≤ 1 / 4 := by linarith
  have H := small_phase_integral_lower_bound μ (fun x : Space n ↦ -(inner ℝ x ξ)) hm hs
  rw [angularFourier_indicator_ball]
  simpa only [Measure.real, μ, Measure.restrict_apply_univ, Complex.ofReal_neg, mul_neg, neg_mul] using H

end OAI.Analysis.Fourier.Restriction
