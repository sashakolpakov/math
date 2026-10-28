import OAI.Analysis.Fourier.BesselPotential.Annular
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace OAI.Analysis.Fourier.BesselPotential

def annularLogBase {n : ℕ} (z : (ℝ × ℝ) × Space n) : ℝ :=
  Real.log (2*z.1.1^2 + Real.sqrt (z.1.1^4 + ‖z.2‖^2))

def annularLogBlend {n : ℕ} (z : (ℝ × ℝ) × Space n) : ℝ :=
  Real.cos z.1.2 ^ 2 + Real.sin z.1.2 ^ 2 * annularLogBase z

/-- Smooth compact-parameter normalization of the inverse logarithmic Bessel
weight. Squared parameters avoid a false differentiability assertion at h=0. -/
def annularLogSobolevSymbol {n : ℕ} (χ : Space n → ℂ) (s B : ℝ)
    (z : (ℝ × ℝ) × Space n) : ℂ :=
  (((z.1.1^4 + ‖z.2‖^2)^(-s/2) * annularLogBlend z ^ (-B) : ℝ) : ℂ) * χ z.2

theorem annularLogBase_pos {n : ℕ} (z : (ℝ × ℝ) × Space n)
    (hz : 1 < ‖z.2‖) : 0 < annularLogBase z := by
  have hs : ‖z.2‖ ≤ Real.sqrt (z.1.1^4 + ‖z.2‖^2) := by
    calc
      ‖z.2‖ = Real.sqrt (‖z.2‖^2) := (Real.sqrt_sq (norm_nonneg z.2)).symm
      _ ≤ _ := Real.sqrt_le_sqrt
        (le_add_of_nonneg_left (show (0:ℝ) ≤ z.1.1^4 by positivity))
  apply Real.log_pos
  linarith [sq_nonneg z.1.1]

theorem annularLogBlend_pos {n : ℕ} (z : (ℝ × ℝ) × Space n)
    (hz : 1 < ‖z.2‖) : 0 < annularLogBlend z := by
  have hl := annularLogBase_pos z hz
  have hi := Real.cos_sq_add_sin_sq z.1.2
  dsimp only [annularLogBlend]
  by_cases hs : Real.sin z.1.2 = 0
  · simpa only [hs,zero_pow (by decide : (2:ℕ)≠0),zero_mul,add_zero] using
      (show 0 < Real.cos z.1.2 ^ 2 by nlinarith)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos (sq_pos_of_ne_zero hs) hl)

theorem tsupport_annularLogSobolevSymbol {n : ℕ} (χ : Space n → ℂ) (s B : ℝ) :
    tsupport (annularLogSobolevSymbol χ s B) ⊆ Set.univ ×ˢ tsupport χ := by
  intro z hz
  refine ⟨trivial,?_⟩
  exact tsupport_comp_subset_preimage χ continuous_snd
    (tsupport_mul_subset_right (f := fun z : (ℝ × ℝ) × Space n =>
      (((z.1.1^4 + ‖z.2‖^2)^(-s/2) * annularLogBlend z ^ (-B) : ℝ) : ℂ)) hz)

theorem contDiff_annularLogSobolevSymbol {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (haway : ∀ ξ ∈ tsupport χ, 1 < ‖ξ‖) (s B : ℝ) :
    ContDiff ℝ ∞ (annularLogSobolevSymbol χ s B) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ tsupport χ
  · have hnorm := haway z.2 hz
    have hb : 0 < z.1.1^4 + ‖z.2‖^2 :=
      add_pos_of_nonneg_of_pos (by positivity) (sq_pos_of_pos (by linarith))
    have hd : ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × Space n =>
        z.1.1^4 + ‖z.2‖^2) z :=
      (contDiffAt_fst.fst.pow 4).add (ContDiffAt.norm_sq (𝕜 := ℝ) contDiffAt_snd)
    have hr := hd.sqrt hb.ne'
    have hh : ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × Space n =>
        2*z.1.1^2 + Real.sqrt (z.1.1^4 + ‖z.2‖^2)) z :=
      (contDiffAt_const.mul (contDiffAt_fst.fst.pow 2)).add hr
    have hhpos : 0 < 2*z.1.1^2 + Real.sqrt (z.1.1^4 + ‖z.2‖^2) :=
      add_pos_of_nonneg_of_pos (by positivity) (Real.sqrt_pos.mpr hb)
    have hlog : ContDiffAt ℝ ∞ annularLogBase z := hh.log hhpos.ne'
    have hblend : ContDiffAt ℝ ∞ annularLogBlend z :=
      (contDiffAt_fst.snd.cos.pow 2).add
        ((contDiffAt_fst.snd.sin.pow 2).mul hlog)
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hd.rpow_const_of_ne hb.ne').mul
        (hblend.rpow_const_of_ne (annularLogBlend_pos z hnorm).ne'))).mul
      (hχ.contDiffAt.comp z contDiffAt_snd)
  · have he := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto
      (continuous_snd.tendsto z)
    have hzero : annularLogSobolevSymbol χ s B =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [he] with q hq
      change χ q.2 = 0 at hq
      simp only [annularLogSobolevSymbol,hq,mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem annularLogSobolevSymbol_uniform_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (haway : ∀ ξ ∈ tsupport χ, 1 < ‖ξ‖) (s B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) (Real.pi/2),
      ∀ h : ℝ, 0 < h → ∀ f : Space n → ℂ, Integrable f →
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ => annularLogSobolevSymbol χ s B (q,ξ))
        h 0 f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume :=
  OAI.Analysis.Fourier.BochnerRiesz.uniform_frequencyHalfWave_zero_bound (isCompact_Icc.prod isCompact_Icc) hc
    (contDiff_annularLogSobolevSymbol hχ haway s B)
    (tsupport_annularLogSobolevSymbol χ s B)

end OAI.Analysis.Fourier.BesselPotential
