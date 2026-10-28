import OAI.Analysis.Fourier.Radial.PositivePower
import OAI.Analysis.Fourier.BochnerRiesz.Basic

open OAI.Analysis.Fourier.Wave

/-! The compact Bochner--Riesz weight and its first derivative. -/

open _root_.MeasureTheory Metric Set
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem bochnerRieszSymbol_unit_eq_positivePower {n : ℕ} (p : ℝ) (x : Space n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 x = positivePower p (1 - ‖x‖ ^ 2) := by
  simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, positivePower, div_one]

theorem bochnerRieszSymbol_unit_zero {n : ℕ} {p : ℝ} (hp : 0 < p)
    {x : Space n} (hx : 1 ≤ ‖x‖) : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 x = 0 := by
  rw [bochnerRieszSymbol_unit_eq_positivePower]
  have hbase : 1 - ‖x‖ ^ 2 ≤ 0 := by nlinarith
  simp only [positivePower, max_eq_right hbase, Real.zero_rpow hp.ne']

theorem hasCompactSupport_bochnerRieszSymbol_unit {n : ℕ} {p : ℝ} (hp : 0 < p) :
    HasCompactSupport (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (n := n) p 1) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space n) 1)
  intro x hx
  apply bochnerRieszSymbol_unit_zero hp
  have h : 1 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
  exact h.le

theorem integrable_bochnerRieszSymbol_unit {n : ℕ} {p : ℝ} (hp : 0 < p) :
    Integrable (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (n := n) p 1) :=
  (OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol hp.le 1).integrable_of_hasCompactSupport
    (hasCompactSupport_bochnerRieszSymbol_unit hp)

theorem contDiff_one_bochnerRieszSymbol_unit {n : ℕ} {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (n := n) p 1) := by
  have hs : ContDiff ℝ 1 (fun x : Space n => (1 : ℝ) - ‖x‖ ^ 2) :=
    contDiff_const.sub (contDiff_norm_sq ℝ)
  have H := (contDiff_positivePower hp).comp hs
  simpa only [Function.comp_def, ← bochnerRieszSymbol_unit_eq_positivePower] using H

theorem hasFDerivAt_bochnerRieszSymbol_unit {n : ℕ} {p : ℝ} (hp : 1 < p)
    (x : Space n) :
    HasFDerivAt (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1)
      ((-2 * p * OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p - 1) 1 x) • innerSL ℝ x) x := by
  have H := (hasDerivAt_positivePower hp (1 - ‖x‖ ^ 2)).comp_hasFDerivAt x
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub 1)
  convert H using 1
  · funext y
    exact bochnerRieszSymbol_unit_eq_positivePower p y
  · ext v
    simp only [smul_apply, smul_eq_mul, neg_apply, ← bochnerRieszSymbol_unit_eq_positivePower]
    ring

theorem fderiv_bochnerRieszSymbol_unit_apply {n : ℕ} {p : ℝ} (hp : 1 < p)
    (x v : Space n) :
    fderiv ℝ (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x v =
      -2 * p * OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p - 1) 1 x * inner ℝ x v := by
  rw [(hasFDerivAt_bochnerRieszSymbol_unit hp x).fderiv]
  rfl

theorem bochnerRieszSymbol_succ {n : ℕ} {p : ℝ} (hp : 0 < p) (x : Space n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p + 1) 1 x =
      (1 - ‖x‖ ^ 2) * OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1 x := by
  by_cases hx : ‖x‖ < 1
  · have hbase : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, div_one, max_eq_left hbase.le,
      Real.rpow_add hbase, Real.rpow_one]
    ring
  · rw [bochnerRieszSymbol_unit_zero (by linarith : 0 < p + 1) (le_of_not_gt hx),
      bochnerRieszSymbol_unit_zero hp (le_of_not_gt hx), mul_zero]

end OAI.Analysis.Fourier.Radial
