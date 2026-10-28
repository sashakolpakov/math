import OAI.Analysis.Fourier.WavePackets.Half.Wave.LowSummation

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal

theorem angularInverse_add_integrable {n : ℕ} {f g : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (f+g) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse f+OAI.Analysis.Fourier.LocalSmoothing.angularInverse g := by
  funext x
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse,mul_add,integral_add (OAI.Analysis.Fourier.LocalSmoothing.integrable_angularKernel_mul hf x)
    (OAI.Analysis.Fourier.LocalSmoothing.integrable_angularKernel_mul hg x),smul_add,Pi.add_apply]

def lowCore {n : ℕ} (χ : Space n → ℂ) (ξ : Space n) := χ ξ*OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ
def highCore {n : ℕ} (χ : Space n → ℂ) (ξ : Space n) := χ ξ*(1-OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ)

theorem lowCore_smooth {n : ℕ} {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (lowCore χ) := hχ.mul (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff _)
theorem highCore_smooth {n : ℕ} {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (highCore χ) := hχ.mul (contDiff_const.sub (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff _))
theorem lowCore_compact {n : ℕ} {χ : Space n → ℂ} (hc : HasCompactSupport χ) :
    HasCompactSupport (lowCore χ) := hc.mul_right
theorem highCore_compact {n : ℕ} {χ : Space n → ℂ} (hc : HasCompactSupport χ) :
    HasCompactSupport (highCore χ) := hc.mul_right
theorem highCore_away {n : ℕ} (χ : Space n → ℂ) : (0 : Space n) ∉ tsupport (highCore χ) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) (by norm_num : (0:ℝ)<1)] with ξ hξ
  have hnorm : ‖ξ‖ ≤ 1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hξ : ‖ξ‖<1).le
  simp only [highCore,OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff_eq_one hnorm,sub_self,mul_zero,Pi.zero_apply]

theorem waveAmplitude_low_decomposition {n : ℕ} (χ : Space n → ℂ) (T : ℝ) :
    waveAmplitude χ 1 T = (lowCore χ+lowRemainder χ T)+waveAmplitude (highCore χ) 1 T := by
  funext ξ
  simp only [lowCore,highCore,lowRemainder,waveAmplitude,div_one,Pi.add_apply]
  ring

theorem inverse_kernel_triple_bound {n : ℕ} {f g h : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h) {A B D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfa : eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse f) 1 volume ≤ .ofReal A)
    (hgb : eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse g) 1 volume ≤ .ofReal B)
    (hhd : eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse h) 1 volume ≤ .ofReal D) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse ((f+g)+h)) 1 volume ≤ .ofReal (A+B+D) := by
  rw [angularInverse_add_integrable (hf.add hg) hh,angularInverse_add_integrable hf hg]
  exact ((eLpNorm_add_le le_rfl).trans (add_le_add (eLpNorm_add_le le_rfl) le_rfl)).trans
    ((add_le_add (add_le_add hfa hgb) hhd).trans_eq (by
      rw [ENNReal.ofReal_add (add_nonneg hA hB) hD,ENNReal.ofReal_add hA hB]))

theorem fixed_smooth_kernel_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ A : ℝ, 0 ≤ A ∧ eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume ≤ .ofReal A := by
  have ht := (memLp_one_iff_integrable.mpr
    (OAI.Analysis.Fourier.BochnerRiesz.integrable_angularInverse_cutoff hχ hc)).eLpNorm_ne_top
  exact ⟨_,ENNReal.toReal_nonneg,le_of_eq (ENNReal.ofReal_toReal ht).symm⟩

/-- Uniform fixed-frequency L¹ bound, including the nonsmooth phase at
the origin. The amplitude may be any smooth compact function. -/
theorem uniform_fixed_frequency_kernel {d : ℕ} {χ : Space (d+1) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T ∈ Icc (1:ℝ) 2,
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (waveAmplitude χ 1 T)) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨A,hA,ha⟩ := fixed_smooth_kernel_bound (lowCore_smooth hχ) (lowCore_compact hc)
  obtain ⟨B,hB,hb⟩ := uniform_lowRemainder_kernel hχ hc
  obtain ⟨D,hD,hd⟩ := uniform_wave_annular_kernel
    (highCore_smooth hχ) (highCore_compact hc) (highCore_away χ)
  refine ⟨A+B+D,by positivity,?_⟩
  intro T hT
  have hai : Integrable (lowCore χ) volume :=
    (lowCore_smooth hχ).continuous.integrable_of_hasCompactSupport (lowCore_compact hc)
  have hdi := waveAmplitude_integrable (highCore_smooth hχ).continuous (highCore_compact hc) 1 T
  rw [waveAmplitude_low_decomposition]
  apply inverse_kernel_triple_bound hai (integrable_lowRemainder hχ.continuous hc T) hdi hA hB hD.le ha (hb T hT)
  rw [← eLpNorm_fourierInv_eq_angularInverse hdi]
  simpa only [Real.one_rpow,mul_one] using hd 1 (by norm_num) le_rfl T hT

theorem uniform_fixed_semiclassicalWaveKernel_L1 {d : ℕ} {χ : Space (d+1) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T ∈ Icc (1:ℝ) 2,
      eLpNorm (fun x => (((2*Real.pi:ℝ):ℂ)^(d+1))⁻¹*
        semiclassicalWaveKernel volume χ 1 T x) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := uniform_fixed_frequency_kernel hχ hc
  refine ⟨C,hC,?_⟩
  intro T hT
  have he := funext (normalized_semiclassicalWaveKernel_eq_angularInverse χ
    (by norm_num : (0:ℝ)<1) T)
  rw [he]
  simpa only [one_smul] using hbound T hT

end OAI.Analysis.Fourier.WavePackets
