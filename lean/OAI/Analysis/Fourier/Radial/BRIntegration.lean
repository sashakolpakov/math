import OAI.Analysis.Fourier.Radial.BRWeight
import OAI.Analysis.Fourier.Radial.BallKernel

open OAI.Analysis.Fourier.Wave

/-! Integration by parts for the compact Bochner--Riesz weight. -/

open _root_.MeasureTheory Metric Set
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem integral_bochnerRiesz_mul_eq_ball {n : ℕ} {p : ℝ} (hp : 0 < p)
    (f : Space n → ℝ) :
    (∫ ξ, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ * f ξ) =
      ∫ ξ, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 ξ * f ξ ∂unitBallVolume n := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hn : 1 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
  rw [bochnerRieszSymbol_unit_zero hp hn.le, zero_mul]

theorem integral_mul_fderiv_compact_real {n : ℕ} {K f : Space n → ℝ}
    (hK : ContDiff ℝ 1 K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (v : Space n) :
    (∫ y, K y * fderiv ℝ f y v) = -∫ y, fderiv ℝ K y v * f y := by
  have hDK : Continuous (fun y => fderiv ℝ K y v) :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDf : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hDK.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left)
    ((hK.continuous.mul hDf).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v).mul_left)
    ((hK.continuous.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left)
    (fun y _ => hK.differentiable one_ne_zero y) (fun y _ => hf.differentiable one_ne_zero y)

theorem fderiv_sine_inner_unit {n : ℕ} {v : Space n} (hv : ‖v‖ = 1)
    (r : ℝ) (y : Space n) :
    fderiv ℝ (fun z => Real.sin (inner ℝ (r • v) z)) y v =
      r * Real.cos (inner ℝ (r • v) y) := by
  have H := ((innerSL ℝ (r • v)).hasFDerivAt (x := y)).sin
  change HasFDerivAt (fun z => Real.sin (inner ℝ (r • v) z))
    (Real.cos (inner ℝ (r • v) y) • innerSL ℝ (r • v)) y at H
  rw [H.fderiv]
  change Real.cos (inner ℝ (r • v) y) * inner ℝ (r • v) v = _
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
  ring

theorem bochnerRiesz_ball_integration_by_parts {n : ℕ} {p : ℝ} (hp : 0 < p)
    {v : Space n} (hv : ‖v‖ = 1) (r : ℝ) :
    r * ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p + 1) 1) (r • v) =
      -2 * (p + 1) * ballCosineLineDeriv (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) 0 v r := by
  have hp1 : 1 < p + 1 := by linarith
  have hK : ContDiff ℝ 1 (fun y : Space n => Real.sin (inner ℝ (r • v) y)) :=
    (innerSL ℝ (r • v)).contDiff.sin
  have H := integral_mul_fderiv_compact_real hK (contDiff_one_bochnerRieszSymbol_unit hp1)
    (hasCompactSupport_bochnerRieszSymbol_unit (by linarith : 0 < p + 1)) v
  simp_rw [fderiv_bochnerRieszSymbol_unit_apply hp1, fderiv_sine_inner_unit hv,
    show p + 1 - 1 = p by ring] at H
  have hleft : (fun y : Space n => Real.sin (inner ℝ (r • v) y) *
      (-2 * (p + 1) * OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 y * inner ℝ y v)) =
      (fun y => (2 * (p + 1)) * (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 y *
        (-(inner ℝ v y) * Real.sin (inner ℝ (r • v) y)))) := by
    funext y
    rw [real_inner_comm y v]
    ring
  have hright : (fun y : Space n => (r * Real.cos (inner ℝ (r • v) y)) *
      OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p + 1) 1 y) =
      (fun y => r * (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p + 1) 1 y *
        Real.cos (inner ℝ (r • v) y))) := by funext y; ring
  rw [hleft, hright, integral_const_mul, integral_const_mul,
    integral_bochnerRiesz_mul_eq_ball hp,
    integral_bochnerRiesz_mul_eq_ball (by linarith : 0 < p + 1)] at H
  have hg : (∫ y, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 y *
      (-(inner ℝ v y) * Real.sin (inner ℝ (r • v) y)) ∂unitBallVolume n) =
      ballCosineLineDeriv (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) 0 v r := by
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [zero_add]
    ring
  rw [hg] at H
  change 2 * (p + 1) * ballCosineLineDeriv (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) 0 v r =
    -(r * ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p + 1) 1) (r • v)) at H
  linarith

end OAI.Analysis.Fourier.Radial
