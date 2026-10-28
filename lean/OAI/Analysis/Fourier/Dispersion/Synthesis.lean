import OAI.Analysis.Fourier.Dispersion.Globalization
import OAI.Analysis.Fourier.Dispersion.LowWeights
import OAI.Analysis.Fourier.Dispersion.L2

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

theorem dispersion_localSmoothing_of_frequency_bound {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) {p : ℝ} (hp : 2≤p) {ε : ℝ}
    (hε : 0<ε ∨ (p=2 ∧ ε=0))
    (hfreq : ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0<h → h≤1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff h z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (C*h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*(1+Real.log (1/h))^(2*n+5))*
        eLpNorm f (ENNReal.ofReal p) volume)
    (hkernel : ∀ χ : Space n → ℂ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ,0<C ∧ ∀ t∈Icc (1:ℝ) 2,
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ Complex.exp (-Complex.I*(t*disp ξ:ℝ))*χ ξ))
          1 volume ≤ ENNReal.ofReal C) :
    ∃ C : ℝ,0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f) (ENNReal.ofReal p) volume ∧
      MemLp (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f) (ENNReal.ofReal p) volume := by
  rcases hε with hε | ⟨rfl,rfl⟩
  · obtain ⟨C,hC,hfreq⟩ := hfreq
    obtain ⟨C₀,hC₀,hlow⟩ := dispersion_low_bessel_bound_of_kernel hd
      (show 1≤p by linarith) (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) hkernel
    have hpp : 1≤ENNReal.ofReal p := by
      simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1≤p by linarith)
    exact dispersion_sobolev_of_frequency_bounds hd hpp ENNReal.ofReal_ne_top
      (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) (2*n+5) hC.le hfreq hε hC₀.le hlow
  · refine ⟨1,by norm_num,fun f ↦ ?_⟩
    simp only [OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder_two,zero_add,OAI.Analysis.Fourier.LocalSmoothing.besselPotential_zero,ENNReal.ofReal_ofNat,
      ENNReal.ofReal_one,one_mul]
    exact ⟨f.memLp 2 volume,dispersionIntegral_spacetime_two_bound hd f⟩

theorem dispersion_logarithmicSobolev_of_frequency_bound {n : ℕ} {disp : Space n → ℝ}
    (hd : Continuous disp) {p B : ℝ} (hp : 2<p) (hB : 2*(n:ℝ)+6<B)
    (hfreq : ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0<h → h≤1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ frequencyDispersion disp OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff h z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (C*h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*(1+Real.log (1/h))^(2*n+5))*
        eLpNorm f (ENNReal.ofReal p) volume)
    (hkernel : ∀ χ : Space n → ℂ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ,0<C ∧ ∀ t∈Icc (1:ℝ) 2,
        eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ Complex.exp (-Complex.I*(t*disp ξ:ℝ))*χ ξ))
          1 volume ≤ ENNReal.ofReal C) :
    ∃ C : ℝ,0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f) (ENNReal.ofReal p) volume ∧
      MemLp (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ dispersionIntegral disp z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f) (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hfreq⟩ := hfreq
  obtain ⟨C₀,hC₀,hlow⟩ := dispersion_low_logBessel_bound_of_kernel hd
    (show 1≤p by linarith) (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B hkernel
  have hpp : 1≤ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1≤p by linarith)
  have hB' : ((2*n+5:ℕ):ℝ)+1<B := by push_cast; linarith
  exact dispersion_log_of_frequency_bounds hd hpp ENNReal.ofReal_ne_top
    (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) (2*n+5) hC.le hfreq hB' hC₀.le hlow

end OAI.Analysis.Fourier.Dispersion
