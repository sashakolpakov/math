import OAI.Analysis.Fourier.BochnerRiesz.Kernel
import OAI.Analysis.Fourier.BochnerRiesz.Dilation
import OAI.Analysis.Fourier.BochnerRiesz.Multiplier
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff Topology

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

/-- The compact family obtained by normalizing a Bessel potential on an
annulus. The parameter λ will be the reciprocal of the frequency scale. -/
def annularSobolevSymbol {n : ℕ} (χ : Space n → ℂ) (σ : ℝ) (z : ℝ × Space n) : ℂ :=
  ((z.1 ^ 2 + ‖z.2‖ ^ 2) ^ (σ / 2) : ℝ) * χ z.2

theorem tsupport_annularSobolevSymbol {n : ℕ} (χ : Space n → ℂ) (σ : ℝ) :
    tsupport (annularSobolevSymbol χ σ) ⊆ Set.univ ×ˢ tsupport χ := by
  intro z hz
  refine ⟨trivial, ?_⟩
  exact tsupport_comp_subset_preimage χ continuous_snd
    (tsupport_mul_subset_right (f := fun z : ℝ × Space n ↦
      (((z.1 ^ 2 + ‖z.2‖ ^ 2) ^ (σ / 2) : ℝ) : ℂ)) hz)

theorem contDiff_annularSobolevSymbol {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hzero : (0 : Space n) ∉ tsupport χ) (σ : ℝ) :
    ContDiff ℝ ∞ (annularSobolevSymbol χ σ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ tsupport χ
  · have hx : z.2 ≠ 0 := by intro h; exact hzero (h ▸ hz)
    have hpos : 0 < z.1 ^ 2 + ‖z.2‖ ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hx))
    have hb : ContDiffAt ℝ ∞ (fun z : ℝ × Space n ↦ z.1 ^ 2 + ‖z.2‖ ^ 2) z :=
      (contDiffAt_fst.pow 2).add (ContDiffAt.norm_sq (𝕜 := ℝ) contDiffAt_snd)
    have hp := hb.rpow_const_of_ne (p := σ / 2) hpos.ne'
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hp).mul (hχ.contDiffAt.comp z contDiffAt_snd)
  · have hnear := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto (continuous_snd.tendsto z)
    have heq : annularSobolevSymbol χ σ =ᶠ[𝓝 z] (fun _ ↦ 0) := by
      filter_upwards [hnear] with q hq
      change χ q.2 = 0 at hq
      simp [annularSobolevSymbol, hq]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem annularSobolevSymbol_kernel_L1_uniform {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        annularSobolevSymbol χ σ (τ, ξ)) ∧
      (∫ x : Space n, ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
        annularSobolevSymbol χ σ (τ, ξ)‖) ≤ C :=
  uniform_fourier_integral_L1 isCompact_Icc hc (contDiff_annularSobolevSymbol hχ hzero σ)
    (tsupport_annularSobolevSymbol χ σ)

theorem annularSobolevSymbol_scaling {n : ℕ} (χ : Space n → ℂ) (σ : ℝ)
    {h : ℝ} (hh : 0 < h) (ξ : Space n) :
    annularSobolevSymbol χ σ (h, h • ξ) =
      (h ^ σ : ℝ) * ((1 + ‖ξ‖ ^ 2) ^ (σ / 2) : ℝ) * χ (h • ξ) := by
  have hs : h ^ 2 + ‖h • ξ‖ ^ 2 = h ^ 2 * (1 + ‖ξ‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    ring
  have hp : (h ^ 2 : ℝ) ^ (σ / 2) = h ^ σ := by
    rw [← Real.rpow_natCast_mul hh.le]
    congr 1
    ring
  simp only [annularSobolevSymbol, hs,
    Real.mul_rpow (sq_nonneg h) (show 0 ≤ 1 + ‖ξ‖ ^ 2 by positivity), hp,
    Complex.ofReal_mul]

theorem besselPotential_eq_annular_multiplier {n : ℕ} (χ : Space n → ℂ) (σ : ℝ)
    {h : ℝ} (hh : 0 < h) (f : Space n → ℂ)
    (hcut : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f x = h ^ (-σ) •
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ annularSobolevSymbol χ σ (h, ξ)) h 0 f x := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.besselPotential, OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave, zero_mul, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul]
  rw [← angularInverse_smul_real]
  congr 1
  funext ξ
  by_cases hz : OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = 0
  · simp [hz]
  rw [annularSobolevSymbol_scaling χ σ hh, hcut ξ hz, mul_one]
  simp only [Complex.real_smul]
  rw [Real.rpow_neg hh.le]
  have hn : h ^ σ ≠ 0 := (Real.rpow_pos_of_pos hh σ).ne'
  simp only [Complex.ofReal_inv]
  field_simp [hn]

theorem annular_besselPotential_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : Space n → ℂ,
      Integrable f → (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f) p volume ≤
        ENNReal.ofReal (C * h ^ (-σ)) * eLpNorm f p volume := by
  obtain ⟨C, hC, hb⟩ := uniform_frequencyHalfWave_zero_bound isCompact_Icc hc
    (contDiff_annularSobolevSymbol hχ hzero σ) (tsupport_annularSobolevSymbol χ σ)
  refine ⟨C, hC, ?_⟩
  intro h hh hone f hf hcut p hp hptop
  have heq : OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f = h ^ (-σ) •
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ ↦ annularSobolevSymbol χ σ (h, ξ)) h 0 f :=
    funext (besselPotential_eq_annular_multiplier χ σ hh f hcut)
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg hh.le _)]
  calc
    _ ≤ ENNReal.ofReal (h ^ (-σ)) * (ENNReal.ofReal C * eLpNorm f p volume) :=
      mul_le_mul' le_rfl (hb h ⟨hh.le, hone⟩ h hh f hf p hp hptop)
    _ = _ := by rw [ENNReal.ofReal_mul hC]; ac_rfl

end OAI.Analysis.Fourier.BochnerRiesz
