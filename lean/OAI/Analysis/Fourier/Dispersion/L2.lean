import OAI.Analysis.Fourier.Dispersion.Dyadic
import OAI.Analysis.Fourier.SquareFunction.ClassicalPlancherel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

theorem dispersionIntegral_eq_fourierInv {n : ℕ} (disp : Space n → ℝ) (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    dispersionIntegral disp t f = 𝓕⁻ (fun ξ ↦
      Complex.exp (-Complex.I*(t*disp ((2*Real.pi)•ξ):ℝ)) * (𝓕 f) ξ) := by
  funext x
  rw [dispersionIntegral,OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  simp only [OAI.Analysis.Fourier.Wave.angularFourier_scaled,SchwartzMap.fourier_coe]

theorem dispersionIntegral_eLpNorm_two {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (dispersionIntegral disp t f) 2 volume = eLpNorm f 2 volume := by
  let g : Space n → ℂ := fun ξ ↦
    Complex.exp (-Complex.I*(t*disp ((2*Real.pi)•ξ):ℝ)) * (𝓕 f) ξ
  have hc : Continuous g := by dsimp only [g]; fun_prop
  have hn (ξ : Space n) : ‖g ξ‖ = ‖(𝓕 f) ξ‖ := by
    simp [g,Complex.norm_exp]
  have he : eLpNorm g 2 volume = eLpNorm (⇑(𝓕 f : SchwartzMap (Space n) ℂ)) 2 volume :=
    eLpNorm_congr_norm_ae hc.aestronglyMeasurable (𝓕 f).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hn)
  have hi : Integrable g := by
    rw [← integrable_norm_iff hc.aestronglyMeasurable]
    simpa only [hn] using (𝓕 f).integrable.norm
  have h2 : MemLp g 2 := by
    change eLpNorm g 2 volume < ⊤
    rw [he]
    exact (𝓕 f).memLp 2 volume
  rw [dispersionIntegral_eq_fourierInv]
  change eLpNorm (𝓕⁻ g) 2 volume = _
  rw [OAI.Analysis.Fourier.SquareFunction.eLpNorm_fourierInv_cycles hi h2,he]
  simpa only [SchwartzMap.fourier_coe] using OAI.Analysis.Fourier.SquareFunction.eLpNorm_fourier_cycles f.integrable (f.memLp 2 volume)

theorem dispersionIntegral_spacetime_two_bound {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) (f : SchwartzMap (Space n) ℂ) :
    MemLp (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1) 2 (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
    eLpNorm (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1) 2 (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      eLpNorm f 2 volume := by
  have hb : eLpNorm (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1)
      (ENNReal.ofReal 2) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ eLpNorm f 2 volume := by
    apply OAI.Analysis.Fourier.LocalSmoothing.Interpolation.observation_norm_le_of_slices
      (continuous_dispersionIntegral hd f).measurable (by norm_num)
    intro t ht
    simpa only [ENNReal.ofReal_ofNat] using (dispersionIntegral_eLpNorm_two hd t f).le
  norm_num only [ENNReal.ofReal_ofNat] at hb
  exact ⟨lt_of_le_of_lt hb (f.memLp 2 volume),hb⟩

end OAI.Analysis.Fourier.Dispersion
