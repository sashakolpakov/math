import OAI.Analysis.Fourier.BochnerRiesz.OperatorPartition
import OAI.Analysis.Fourier.BochnerRiesz.FiniteNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem eLpNorm_weighted_brShellPacket_le {n : ℕ} {δ σ C K : ℝ}
    {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hzero : 0 ∉ tsupport χ) (hK : 0 ≤ K) (_ : 0 ≤ C)
    (hkernel : eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (brExteriorSymbol δ χ)) 1 volume ≤ ENNReal.ofReal K)
    (j : ℕ) (f : SchwartzMap (Space n) ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hshell : eLpNorm (maximalShellCycles (dyadicPowerProfile δ) ((2 : ℝ) ^ j) f) p volume ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ σ) * eLpNorm f p volume) :
    eLpNorm (fun x ↦ Complex.ofReal (((2 : ℝ) ^ j) ^ (-δ)) * brShellPacket δ χ j f x) p volume ≤
      ENNReal.ofReal ((K * C) * (((2 : ℝ) ^ j) ^ (-δ) * ((2 : ℝ) ^ j) ^ σ)) * eLpNorm f p volume := by
  have H := eLpNorm_smooth_dilatedShell_le (contDiff_brExteriorSymbol δ hχ hzero)
    (hasCompactSupport_brExteriorSymbol δ hc) (dyadicPowerProfile δ) ((2 : ℝ) ^ j)
    (show 0 < 2 * Real.pi * (2 : ℝ) ^ j by positivity) f hp hpt
  have H' : eLpNorm (brShellPacket δ χ j f) p volume ≤
      ENNReal.ofReal K * (ENNReal.ofReal (C * ((2 : ℝ) ^ j) ^ σ) * eLpNorm f p volume) :=
    H.trans (mul_le_mul' hkernel hshell)
  change eLpNorm ((Complex.ofReal (((2 : ℝ) ^ j) ^ (-δ))) • brShellPacket δ χ j f) p volume ≤ _
  rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ j) ^ (-δ))]
  apply (mul_le_mul' le_rfl H').trans_eq
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

theorem exists_angularInverse_kernel_bound {n : ℕ} {a : Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ∃ K : ℝ, 0 < K ∧ eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse a) 1 volume ≤ ENNReal.ofReal K := by
  let D := eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse a) 1 volume
  have hD : D ≠ ⊤ := (memLp_one_iff_integrable.mpr (integrable_angularInverse_cutoff ha hc)).eLpNorm_ne_top
  refine ⟨D.toReal + 1, by positivity, ?_⟩
  calc
    D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

end OAI.Analysis.Fourier.BochnerRiesz
