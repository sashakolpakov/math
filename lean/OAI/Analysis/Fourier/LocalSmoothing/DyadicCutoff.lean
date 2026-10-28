import OAI.Analysis.Fourier.BochnerRiesz.Projection
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open OAI.Analysis.Fourier.Wave

open Set Metric Filter _root_.MeasureTheory
open scoped ContDiff Topology

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

/-- The low-frequency cutoff for the inhomogeneous frequency decomposition. -/
def smoothingLowBump (n : ℕ) : ContDiffBump (0 : Space n) where
  rIn := 8
  rOut := 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def smoothingLowCutoff {n : ℕ} (ξ : Space n) : ℂ := smoothingLowBump n ξ

/-- Its dilated differences give the annular pieces, at scales `2⁻ʲ`. -/
def smoothingAnnularCutoff {n : ℕ} (ξ : Space n) : ℂ :=
  smoothingLowCutoff ((1 / 2 : ℝ) • ξ) - smoothingLowCutoff ξ

def smoothingDyadicScale (j : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ j

theorem smoothingDyadicScale_pos (j : ℕ) : 0 < smoothingDyadicScale j := by
  unfold smoothingDyadicScale
  positivity

theorem smoothingDyadicScale_le_one (j : ℕ) : smoothingDyadicScale j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem smoothingDyadicScale_succ (j : ℕ) :
    smoothingDyadicScale (j + 1) = (1 / 2 : ℝ) * smoothingDyadicScale j := by
  simp only [smoothingDyadicScale, pow_succ]
  ring

theorem contDiff_smoothingLowCutoff (n : ℕ) :
    ContDiff ℝ ∞ (@smoothingLowCutoff n) :=
  Complex.ofRealCLM.contDiff.comp (smoothingLowBump n).contDiff

theorem hasCompactSupport_smoothingLowCutoff (n : ℕ) :
    HasCompactSupport (@smoothingLowCutoff n) := by
  exact (smoothingLowBump n).hasCompactSupport.comp_left rfl

theorem smoothingLowCutoff_eq_one {n : ℕ} {ξ : Space n} (hξ : ‖ξ‖ ≤ 1) :
    smoothingLowCutoff ξ = 1 := by
  have hξ' : ‖ξ‖ ≤ 8 := hξ.trans (by norm_num)
  have h := (smoothingLowBump n).one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, smoothingLowBump] using hξ')
  simp only [smoothingLowCutoff, h, Complex.ofReal_one]

theorem norm_smoothingLowCutoff_le_one {n : ℕ} (ξ : Space n) :
    ‖smoothingLowCutoff ξ‖ ≤ 1 := by
  simpa only [smoothingLowCutoff, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (smoothingLowBump n).nonneg] using
    (smoothingLowBump n).le_one (x := ξ)

theorem contDiff_smoothingAnnularCutoff (n : ℕ) :
    ContDiff ℝ ∞ (@smoothingAnnularCutoff n) := by
  have hd : ContDiff ℝ ∞ (fun ξ : Space n ↦ (1 / 2 : ℝ) • ξ) :=
    contDiff_id.const_smul _
  exact ((contDiff_smoothingLowCutoff n).comp hd).sub (contDiff_smoothingLowCutoff n)

theorem hasCompactSupport_smoothingAnnularCutoff (n : ℕ) :
    HasCompactSupport (@smoothingAnnularCutoff n) :=
  ((hasCompactSupport_smoothingLowCutoff n).comp_smul (by norm_num : (1 / 2 : ℝ) ≠ 0)).sub
    (hasCompactSupport_smoothingLowCutoff n)

theorem smoothingAnnularCutoff_eq_zero {n : ℕ} {ξ : Space n} (hξ : ‖ξ‖ ≤ 1) :
    smoothingAnnularCutoff ξ = 0 := by
  have hh : ‖(1 / 2 : ℝ) • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [norm_nonneg ξ]
  simp only [smoothingAnnularCutoff, smoothingLowCutoff_eq_one hh,
    smoothingLowCutoff_eq_one hξ, sub_self]

theorem zero_notMem_tsupport_smoothingAnnularCutoff (n : ℕ) :
    (0 : Space n) ∉ tsupport smoothingAnnularCutoff := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) (by norm_num : (0 : ℝ) < 1)] with ξ hξ
  exact smoothingAnnularCutoff_eq_zero (le_of_lt (by
    simpa only [mem_ball, dist_zero_right] using hξ))

/-- The finite partition is an exact telescoping identity, before taking limits. -/
theorem smoothing_dyadic_partition {n : ℕ} (N : ℕ) (ξ : Space n) :
    smoothingLowCutoff ξ +
      ∑ j ∈ Finset.range N, smoothingAnnularCutoff (smoothingDyadicScale j • ξ) =
        smoothingLowCutoff (smoothingDyadicScale N • ξ) := by
  induction N with
  | zero => simp [smoothingDyadicScale]
  | succ N hN =>
    rw [Finset.sum_range_succ, ← add_assoc, hN]
    simp only [smoothingAnnularCutoff, smul_smul, smoothingDyadicScale_succ]
    ring

theorem eventually_smoothingLowCutoff_dyadic_eq_one {n : ℕ} (ξ : Space n) :
    ∀ᶠ N : ℕ in atTop, smoothingLowCutoff (smoothingDyadicScale N • ξ) = 1 := by
  have hscale : Tendsto smoothingDyadicScale atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hz : Tendsto (fun N ↦ smoothingDyadicScale N • ξ) atTop (𝓝 (0 : Space n)) := by
    simpa only [zero_smul] using hscale.smul_const ξ
  filter_upwards [hz.eventually (Metric.ball_mem_nhds (0 : Space n)
    (by norm_num : (0 : ℝ) < 1))] with N hN
  exact smoothingLowCutoff_eq_one (le_of_lt (by
    simpa only [mem_ball, dist_zero_right] using hN))

theorem tendsto_smoothing_dyadic_partition {n : ℕ} (ξ : Space n) :
    Tendsto (fun N : ℕ ↦ smoothingLowCutoff ξ +
      ∑ j ∈ Finset.range N, smoothingAnnularCutoff (smoothingDyadicScale j • ξ))
      atTop (𝓝 1) := by
  simp only [smoothing_dyadic_partition]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_smoothingLowCutoff_dyadic_eq_one ξ] with N hN
  exact hN.symm

end OAI.Analysis.Fourier.LocalSmoothing
