import OAI.Analysis.Fourier.LocalSmoothing.Globalization
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Basic
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.LocalSmoothingLowFrequency

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

/-- The frequency-localized logarithmic refinement gives the exact
positive-loss local-smoothing theorem, including its zero-loss L² case. -/
theorem euclideanLocalSmoothing_of_logarithmicRefinement
    (hlog : LogarithmicRefinement) : EuclideanLocalSmoothing := by
  intro n hn p ε hp hε
  rcases hε with hε | ⟨rfl, rfl⟩
  · obtain ⟨C,hC,hfreq⟩ := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.frequency_bound_of_logarithmicRefinement
      hlog hn hp (contDiff_smoothingAnnularCutoff n)
      (hasCompactSupport_smoothingAnnularCutoff n) (zero_notMem_tsupport_smoothingAnnularCutoff n)
    obtain ⟨C₀,hC₀,hlow⟩ := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.lowFrequency_bessel_bound
      (show 0 < n by omega) (show 1 ≤ p by linarith) (smoothingOrder n p + ε)
    have hpp : 1 ≤ ENNReal.ofReal p := by
      simpa only [← ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
    exact localSmoothing_sobolev_of_frequency_bounds hpp ENNReal.ofReal_ne_top
      (smoothingOrder n p) (2*n+5) hC.le
      (fun h hh h1 f ↦ (hfreq h hh h1 f).2) hε hC₀.le hlow
  · refine ⟨1, by norm_num, ?_⟩
    intro f
    simpa only [add_zero, ENNReal.ofReal_ofNat, ENNReal.ofReal_one, one_mul] using
      localSmoothing_two f

/-- The same refinement gives the sharp logarithmic Sobolev conclusion
throughout its strict range `B>2n+6`. -/
theorem logarithmicSobolev_of_logarithmicRefinement
    (hlog : LogarithmicRefinement) : LogarithmicSobolev := by
  intro n hn p B hp hB
  obtain ⟨C,hC,hfreq⟩ := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.frequency_bound_of_logarithmicRefinement
    hlog hn hp.le (contDiff_smoothingAnnularCutoff n)
    (hasCompactSupport_smoothingAnnularCutoff n) (zero_notMem_tsupport_smoothingAnnularCutoff n)
  obtain ⟨C₀,hC₀,hlow⟩ := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.lowFrequency_logBessel_bound
    (show 0 < n by omega) (show 1 ≤ p by linarith) (smoothingOrder n p) B
  have hpp : 1 ≤ ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hB' : ((2*n+5 : ℕ) : ℝ) + 1 < B := by
    push_cast
    linarith
  exact localSmoothing_log_of_frequency_bounds hpp ENNReal.ofReal_ne_top
    (smoothingOrder n p) (2*n+5) hC.le
    (fun h hh h1 f ↦ (hfreq h hh h1 f).2) hB' hC₀.le hlow

end OAI.Analysis.Fourier.LocalSmoothing
