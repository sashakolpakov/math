import OAI.Analysis.Fourier.BochnerRiesz.KernelDilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


theorem integrable_top_convolution_integrand {n : ℕ} {K : Space n → ℂ}
    (hK : Integrable K) (f : BrLp n ∞) (x : Space n) :
    Integrable (fun y => K y * f (x - y)) := by
  have hf : MemLp (fun y => f (x - y)) ∞ volume :=
    (Lp.memLp f).comp_measurePreserving ((volume : Measure (Space n)).measurePreserving_sub_left x)
  exact (memLp_one_iff_integrable.mpr hK).integrable_mul hf

theorem memLp_top_complexConvolution {n : ℕ} {K : Space n → ℂ}
    (hK : Integrable K) (f : BrLp n ∞) :
    MemLp (OAI.Analysis.Fourier.WavePackets.complexConvolution K f volume) ∞ volume := by
  apply (OAI.Analysis.Fourier.Radial.eLpNorm_complexConvolution_top_le hK.aestronglyMeasurable (Lp.aestronglyMeasurable f)).trans_lt
  exact ENNReal.mul_lt_top (memLp_one_iff_integrable.mpr hK) (Lp.memLp f)

def convolutionTop {n : ℕ} {K : Space n → ℂ} (hK : Integrable K)
    (f : BrLp n ∞) : BrLp n ∞ := (memLp_top_complexConvolution hK f).toLp _

theorem convolutionTop_coe {n : ℕ} {K : Space n → ℂ} (hK : Integrable K) (f : BrLp n ∞) :
    (convolutionTop hK f : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.WavePackets.complexConvolution K f volume :=
  (memLp_top_complexConvolution hK f).coeFn_toLp

theorem convolutionTop_add {n : ℕ} {K : Space n → ℂ} (hK : Integrable K) (f g : BrLp n ∞) :
    convolutionTop hK (f + g) = convolutionTop hK f + convolutionTop hK g := by
  apply Lp.ext
  filter_upwards [convolutionTop_coe hK (f + g), convolutionTop_coe hK f,
    convolutionTop_coe hK g, Lp.coeFn_add (convolutionTop hK f) (convolutionTop hK g)] with x hfg hf hg hadd
  rw [hfg, hadd, Pi.add_apply, hf, hg]
  unfold OAI.Analysis.Fourier.WavePackets.complexConvolution
  rw [← integral_add (integrable_top_convolution_integrand hK f x)
    (integrable_top_convolution_integrand hK g x)]
  apply integral_congr_ae
  filter_upwards [((volume : Measure (Space n)).measurePreserving_sub_left x).quasiMeasurePreserving.ae
    (Lp.coeFn_add f g)] with y hy
  rw [hy, Pi.add_apply, mul_add]

theorem convolutionTop_smul {n : ℕ} {K : Space n → ℂ} (hK : Integrable K)
    (c : ℂ) (f : BrLp n ∞) : convolutionTop hK (c • f) = c • convolutionTop hK f := by
  apply Lp.ext
  filter_upwards [convolutionTop_coe hK (c • f), convolutionTop_coe hK f,
    Lp.coeFn_smul c (convolutionTop hK f)] with x hcf hf hsmul
  rw [hcf, hsmul, Pi.smul_apply, hf]
  unfold OAI.Analysis.Fourier.WavePackets.complexConvolution
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [((volume : Measure (Space n)).measurePreserving_sub_left x).quasiMeasurePreserving.ae
    (Lp.coeFn_smul c f)] with y hy
  rw [hy, Pi.smul_apply]
  simp only [smul_eq_mul]
  ring

theorem norm_convolutionTop_le {n : ℕ} {K : Space n → ℂ} (hK : Integrable K) (f : BrLp n ∞) :
    ‖convolutionTop hK f‖ ≤ (eLpNorm K 1 volume).toReal * ‖f‖ := by
  have H := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (memLp_one_iff_integrable.mpr hK).ne (Lp.memLp f).ne)
    (OAI.Analysis.Fourier.Radial.eLpNorm_complexConvolution_top_le hK.aestronglyMeasurable (Lp.aestronglyMeasurable f))
  rw [Lp.norm_def, eLpNorm_congr_ae (convolutionTop_coe hK f), Lp.norm_def]
  simpa only [ENNReal.toReal_mul] using H

def convolutionTopCLM {n : ℕ} {K : Space n → ℂ} (hK : Integrable K) : BrLp n ∞ →L[ℂ] BrLp n ∞ :=
  LinearMap.mkContinuous
    { toFun := convolutionTop hK
      map_add' := convolutionTop_add hK
      map_smul' := convolutionTop_smul hK }
    (eLpNorm K 1 volume).toReal (norm_convolutionTop_le hK)

theorem convolutionTopCLM_norm {n : ℕ} {K : Space n → ℂ} (hK : Integrable K) :
    ‖convolutionTopCLM hK‖ ≤ (eLpNorm K 1 volume).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
  exact norm_convolutionTop_le hK

theorem eLpNorm_brDilatedKernel_one {n : ℕ} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    eLpNorm (brDilatedKernel (n := n) δ R) 1 volume = eLpNorm (OAI.Analysis.Fourier.Radial.bochnerRieszKernel (n := n) δ) 1 volume := by
  rw [brDilatedKernel_eq_angularInverse δ hR]
  exact eLpNorm_angularInverse_dilate_one (OAI.Analysis.Fourier.Radial.integrable_complex_bochnerRieszSymbol_unit hδ) (inv_pos.mpr hR)

theorem integrable_brDilatedKernel {n : ℕ} (hn : 1 ≤ n) {δ R : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) (hR : 0 < R) : Integrable (brDilatedKernel (n := n) δ R) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  apply memLp_one_iff_integrable.mp
  change eLpNorm (brDilatedKernel δ R) 1 volume < ⊤
  rw [eLpNorm_brDilatedKernel_one hd hR]
  exact memLp_one_iff_integrable.mpr (OAI.Analysis.Fourier.Radial.integrable_bochnerRieszKernel hn hδ)

/-- The `L∞` endpoint is realized by the classical integrable convolution
kernel on the full essentially bounded function space. -/
theorem bochnerRiesz_Linfty_operators {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : Ioi (0 : ℝ) → BrLp n ∞ →L[ℂ] BrLp n ∞,
      (∀ R, ‖T R‖ ≤ C) ∧
      (∀ R f, (T R f : Space n → ℂ) =ᵐ[volume]
        OAI.Analysis.Fourier.WavePackets.complexConvolution (brDilatedKernel δ R.val) f volume) ∧
      (∀ R (f : SchwartzMap (Space n) ℂ),
        (T R (f.toLp ∞ volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  let A := (eLpNorm (OAI.Analysis.Fourier.Radial.bochnerRieszKernel (n := n) δ) 1 volume).toReal
  let T (R : Ioi (0 : ℝ)) := convolutionTopCLM (integrable_brDilatedKernel hn hδ R.property)
  refine ⟨A + 1, by dsimp [A]; positivity, T, ?_, ?_, ?_⟩
  · intro R
    apply (convolutionTopCLM_norm _).trans
    rw [eLpNorm_brDilatedKernel_one hd R.property]
    change A ≤ A + 1
    linarith
  · intro R f
    exact convolutionTop_coe (integrable_brDilatedKernel hn hδ R.property) f
  · intro R f
    filter_upwards [convolutionTop_coe (integrable_brDilatedKernel hn hδ R.property) (f.toLp ∞ volume)] with x hx
    change convolutionTop (integrable_brDilatedKernel hn hδ R.property) (f.toLp ∞ volume) x = _
    rw [hx, bochnerRiesz_eq_convolve_brDilatedKernel hd R.property f.integrable,
      OAI.Analysis.Fourier.SquareFunction.convolveKernel_commuted]
    unfold OAI.Analysis.Fourier.WavePackets.complexConvolution
    apply integral_congr_ae
    filter_upwards [((volume : Measure (Space n)).measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (f.coeFn_toLp ∞ volume)] with y hy
    rw [hy]
    simp only [smul_eq_mul, mul_comm]

end OAI.Analysis.Fourier.BochnerRiesz
