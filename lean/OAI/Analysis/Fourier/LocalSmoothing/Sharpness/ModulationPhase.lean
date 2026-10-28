import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.AnnularWeights
import OAI.Analysis.Fourier.Restriction.Modulation
import Mathlib.Analysis.SpecificLimits.Basic

open OAI.Analysis.Fourier.Wave

noncomputable section
open Filter _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

/-- Exact rationalization of the modulated wave phase. -/
theorem modulation_phase_identity {n : ℕ} {ω : Space n} (hω : ‖ω‖ = 1)
    (ξ : Space n) {N : ℝ} (hN : 0 < N) :
    ‖N • ω + ξ‖ - N =
      (2 * inner ℝ ω ξ + ‖ξ‖^2/N) / (‖ω + N⁻¹ • ξ‖ + 1) := by
  have hvec : N • (ω + N⁻¹ • ξ) = N • ω + ξ := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ hN.ne',one_smul]
  have hnorm : ‖N • ω + ξ‖ = N * ‖ω + N⁻¹ • ξ‖ := by
    rw [← hvec,norm_smul,Real.norm_eq_abs,abs_of_pos hN]
  have hsq := norm_add_sq_real ω (N⁻¹ • ξ)
  rw [hω,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hN)] at hsq
  rw [hnorm]
  apply (eq_div_iff (show ‖ω + N⁻¹ • ξ‖ + 1 ≠ 0 by positivity)).mpr
  field_simp [hN.ne'] at hsq ⊢
  nlinarith

/-- A fixed translated Fourier variable sees a linear phase at infinite
modulation frequency. This is the rigidly travelling bump limit. -/
theorem tendsto_modulation_phase {n : ℕ} {ω : Space n} (hω : ‖ω‖ = 1)
    (ξ : Space n) :
    Tendsto (fun N : ℝ => ‖N • ω + ξ‖ - N) atTop (𝓝 (inner ℝ ω ξ)) := by
  have hinv : Tendsto (fun N : ℝ => N⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hv : Tendsto (fun N : ℝ => ω + N⁻¹ • ξ) atTop (𝓝 ω) := by
    simpa using tendsto_const_nhds.add (hinv.smul_const ξ)
  have hden : Tendsto (fun N : ℝ => ‖ω + N⁻¹ • ξ‖ + 1) atTop (𝓝 (2:ℝ)) := by
    simpa only [hω,one_add_one_eq_two] using hv.norm.add_const 1
  have hnum : Tendsto (fun N : ℝ => 2 * inner ℝ ω ξ + ‖ξ‖^2/N)
      atTop (𝓝 (2 * inner ℝ ω ξ)) := by
    simpa only [div_eq_mul_inv,mul_zero,add_zero] using
      tendsto_const_nhds.add (hinv.const_mul (‖ξ‖^2))
  have h := hnum.div hden (by norm_num : (2:ℝ) ≠ 0)
  have hlim : Tendsto (fun N : ℝ =>
      (2 * inner ℝ ω ξ + ‖ξ‖^2/N) / (‖ω + N⁻¹ • ξ‖ + 1))
      atTop (𝓝 (inner ℝ ω ξ)) := by convert h using 1 ; ring_nf
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
  exact (modulation_phase_identity hω ξ hN).symm

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
