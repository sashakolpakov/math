import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Young
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Density
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Exponents

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem frequencyWave_schwartz_bound_extends {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {p : ℝ} (hp : 1 ≤ p) {A K : ℝ≥0∞} (hA : A ≠ ⊤) (hK : K ≠ ⊤)
    (hkernel : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (waveKernel φ h t) 1 volume ≤ K)
    (hsharp : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 g z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A * eLpNorm g (.ofReal p) volume)
    {f : Space n → ℂ} (hf : Measurable f) (hi : Integrable f) (hfp : MemLp f (.ofReal p) volume) :
    eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
      (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A * eLpNorm f (.ofReal p) volume := by
  apply bound_of_schwartz_dense (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n)
    (fun g z => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 g z.1)
    (fun g k hg hk z => frequencyHalfWave_add hφ hs hh z.2 hg hk z.1)
    (by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top hA hK hsharp
    (fun g hg hi _ => frequencyWave_spacetime_young hφ hs hh hg hi hp hkernel) hf hi hfp

structure FrequencyEndpoints (n : ℕ) (φ : Space n → ℂ) where
  twoConstant : ℝ
  criticalConstant : ℝ
  infinityConstant : ℝ
  two_pos : 0 < twoConstant
  critical_pos : 0 < criticalConstant
  infinity_pos : 0 < infinityConstant
  two : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : Space n → ℂ,
    Measurable f → Integrable f → MemLp f 2 volume →
    eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) 2 (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal twoConstant * eLpNorm f 2 volume
  critical : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : Space n → ℂ,
    Measurable f → Integrable f → MemLp f (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume →
    eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
      (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (criticalConstant * (1 + Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume
  infinity : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : Space n → ℂ,
    Measurable f → Integrable f → ∀ M : ℝ, 0 < M → (∀ x, ‖f x‖ ≤ M) →
    ∀ᵐ z : Space n × ℝ ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n, ‖OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1‖ ≤
      (infinityConstant * h ^ (-((n:ℝ)-1)/2)) * M

theorem frequency_endpoints_of_logarithmicRefinement (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    Nonempty (FrequencyEndpoints n φ) := by
  obtain ⟨A,hA,h2⟩ := frequencyWave_two hφ hs
  obtain ⟨B,hB,hc⟩ := hlog n hn φ hφ hs hz
  obtain ⟨K,hK,hk⟩ := uniform_waveKernel_L1 (by omega : 0 < n) hφ hs hz
  refine ⟨⟨A,B,K,hA,hB,hK,?_,?_,?_⟩⟩
  · intro h hh h1 f hf hi hp
    have H := frequencyWave_schwartz_bound_extends hφ.continuous hs hh
      (p := 2) (by norm_num) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (hk h hh h1) (fun g => by simpa using (h2 h hh g).2) hf hi (by simpa using hp)
    simpa using H
  · intro h hh h1 f hf hi hp
    exact frequencyWave_schwartz_bound_extends hφ.continuous hs hh
      (by linarith [criticalExponent_gt_two hn]) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (hk h hh h1) (fun g => (hc h hh h1 g).2) hf hi hp
  · intro h hh h1 f hf hi M hM hb
    exact frequencyWave_ae_bounded hφ.continuous hs hh hi hM.le
      (mul_nonneg hK.le (Real.rpow_nonneg hh.le _)) (hk h hh h1) hb

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
