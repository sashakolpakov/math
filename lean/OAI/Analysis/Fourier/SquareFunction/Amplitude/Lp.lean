import OAI.Analysis.Fourier.SquareFunction.Amplitude.Continuity
import OAI.Analysis.Fourier.SquareFunction.Minkowski

open OAI.Analysis.Fourier.Wave

/-! Synthesis of the separated amplitude estimates in spatial `Lᵖ`. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

noncomputable def separationMass : ℝ≥0∞ :=
  ∫⁻ η : ℝ, ENNReal.ofReal ((1 + |η|) ^ (-2 : ℝ))

theorem separationMass_ne_top : separationMass ≠ ⊤ := by
  have h := integrable_separation_weight.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at h
  have hn (η : ℝ) : 0 ≤ (1 + |η|) ^ (-2 : ℝ) := by positivity
  simpa only [separationMass, Real.enorm_eq_ofReal (hn _)] using h.ne

theorem eLpNorm_amplitudeShellHilbert_synthesis {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) {p : ℝ} (hp : 1 ≤ p) {B : ℝ≥0∞}
    (hb : ∀ η : ℝ, eLpNorm (thinShellHilbert φ δ (amplitudeInput A η f))
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ((1 + |η|) ^ (-2 : ℝ)) * B) :
    eLpNorm (amplitudeShellHilbert A hA.continuous φ δ f) (ENNReal.ofReal p) volume ≤
      separationMass * B := by
  let : MeasurableSpace RadiusHilbert := borel RadiusHilbert
  let : BorelSpace RadiusHilbert := ⟨rfl⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let F : Space n × ℝ → RadiusHilbert :=
    fun z => radiusToL2 (separatedShellOutput A φ δ f z)
  have hF : Continuous F := continuous_separatedShellHilbert hA hc φ δ f
  apply eLpNorm_integral_domination_of_slice_bound hF.measurable
    (w := fun η : ℝ => (1 + |η|) ^ (-2 : ℝ)) (by fun_prop) (fun η => by positivity)
    (continuous_amplitudeShellHilbert A hA.continuous hc φ δ f).aestronglyMeasurable hp
  · intro η
    have he : eLpNorm (fun x => F (x, η)) (ENNReal.ofReal p) volume =
        eLpNorm (thinShellHilbert φ δ (amplitudeInput A η f)) (ENNReal.ofReal p) volume := by
      apply eLpNorm_congr_enorm_ae (continuous_left_slice hF η).aestronglyMeasurable
        (continuous_thinShellHilbert φ δ (amplitudeInput A η f)).aestronglyMeasurable
      filter_upwards [] with x
      exact enorm_radiusToL2_modulation η _
    rw [he]
    exact hb η
  · intro x
    rw [amplitudeShellHilbert_eq_integral hA hc]
    exact enorm_integral_le_lintegral_enorm _

end OAI.Analysis.Fourier.SquareFunction
