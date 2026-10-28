import OAI.Analysis.Fourier.SquareFunction.Amplitude.Reconstruction

open OAI.Analysis.Fourier.Wave

/-! Jointly continuous representatives of the separated shell family. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff

theorem continuous_separatedShellOutput {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) : Continuous (separatedShellOutput A φ δ f) := by
  obtain ⟨C, hC, hb⟩ := amplitudeInput_bound hA hc
  let B := SchwartzMap.seminorm ℝ 0 0 φ
  let F : (Space n × ℝ) → Space n → C(RadiusInterval, ℂ) :=
    fun z ξ => separatedShellIntegrand A φ δ f z.1 (z.2, ξ)
  have he : separatedShellOutput A φ δ f = fun z => ∫ ξ, F z ξ := by
    funext z
    exact (integral_separatedShellIntegrand_space hA hc φ δ f z.1 z.2).symm
  rw [he]
  have hm (z : Space n × ℝ) : AEStronglyMeasurable (F z) volume :=
    (integrable_separatedShellIntegrand_slice hA hc φ δ f z.1 z.2).aestronglyMeasurable
  have hbound (z : Space n × ℝ) (ξ : Space n) : ‖F z ξ‖ ≤ C * (B * ‖(𝓕 f) ξ‖) := by
    have hw : (1 + |z.2|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z.2]) (by norm_num)
    calc
      _ ≤ (C * (1 + |z.2|) ^ (-2 : ℝ)) * (B * ‖(𝓕 f) ξ‖) :=
        norm_separatedShellIntegrand_le A φ δ f z.1 (z.2, ξ) ((hb z.2).1 ξ)
      _ ≤ (C * 1) * (B * ‖(𝓕 f) ξ‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hC)
          (mul_nonneg (apply_nonneg _ _) (norm_nonneg _))
      _ = _ := by rw [mul_one]
  have hcont (ξ : Space n) : Continuous (fun z : Space n × ℝ => F z ξ) := by
    have hp : Continuous (fun x : Space n => spatialPhase x ξ) := by
      unfold spatialPhase
      fun_prop
    have hs : Continuous (fun η => separatedAmplitudeSymbol A φ δ η ξ) :=
      continuous_left_slice (continuous_separatedAmplitudeSymbol hA hc φ δ) ξ
    exact (hp.comp continuous_fst).smul
      ((hs.comp continuous_snd).const_smul (𝓕 (f : Space n → ℂ) ξ))
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ => C * (B * ‖(𝓕 f) ξ‖))
  · exact Filter.Eventually.of_forall hm
  · exact Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall (hbound z)
  · exact ((𝓕 f).integrable.norm.const_mul B).const_mul C
  · exact Filter.Eventually.of_forall fun ξ => (hcont ξ).tendsto z

theorem continuous_separatedShellHilbert {n : ℕ} {A : ℝ × Space n → ℂ}
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A) (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ => radiusToL2 (separatedShellOutput A φ δ f z)) :=
  radiusToL2.continuous.comp (continuous_separatedShellOutput hA hc φ δ f)

end OAI.Analysis.Fourier.SquareFunction
