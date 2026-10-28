import OAI.Analysis.Fourier.SquareFunction.EuclideanSharp
import OAI.Analysis.Fourier.SquareFunction.EuclideanMaximal

open OAI.Analysis.Fourier.Wave

/-! Extended-nonnegative envelopes for the cube sharp inequality. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set BoxIntegral Metric
open scoped ENNReal

theorem eLpNorm_toReal_eq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {G : X → ℝ≥0∞} (hG : Measurable G) (hGtop : ∀ x, G x ≠ ∞) (p : ℝ≥0∞) :
    eLpNorm (fun x => (G x).toReal) p μ = eLpNorm G p μ := by
  apply eLpNorm_congr_enorm_ae (hG.ennreal_toReal.aestronglyMeasurable) hG.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hGtop x), enorm_eq_self]

theorem eLpNorm_le_of_centered_envelope {n : ℕ} [NeZero n]
    (f : Space n → ℝ) (G : Space n → ℝ≥0∞) (hfn : ∀ x, 0 ≤ f x)
    (hfc : Continuous f) (hf : Integrable f) (hG : Measurable G) (hGtop : ∀ x, G x ≠ ∞)
    {p γ : ℝ} (hp : 1 < p) (hγ : 0 < γ)
    (hsmall : γ * ((2 : ℝ) ^ n + 1) ^ p < 1)
    (hosc : ∀ Q : Box (Fin n), IsCubeBox Q → ∃ c : ℝ, ∀ x ∈ euclideanBox Q,
      (∫⁻ y in euclideanBox Q, ‖f y - c‖ₑ) / volume (euclideanBox Q) ≤ G x) :
    eLpNorm f (ENNReal.ofReal p) volume ≤
      2 * ((ENNReal.ofReal (1 / (1 - γ * ((2 : ℝ) ^ n + 1) ^ p))) ^ (1 / p) *
        ENNReal.ofReal (((2 : ℝ) ^ n + 1) / γ)) *
          eLpNorm G (ENNReal.ofReal p) volume := by
  have h := eLpNorm_le_of_euclidean_centered_oscillation f (fun x => (G x).toReal)
    hfn (fun _ => ENNReal.toReal_nonneg) hfc hf hG.ennreal_toReal.aestronglyMeasurable
    hp hγ hsmall ?_
  · rwa [eLpNorm_toReal_eq volume hG hGtop] at h
  · intro Q hQ
    obtain ⟨c, hc⟩ := hosc Q hQ
    refine ⟨c, fun x hx => ?_⟩
    simpa only [ENNReal.ofReal_toReal (hGtop x)] using hc x hx

theorem ballMaximal_ne_top_of_bounded {n : ℕ} {f : Space n → ℝ≥0∞}
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hf : ∀ x, f x ≤ C) (x : Space n) :
    ballMaximal volume f x ≠ ∞ := by
  exact ne_top_of_le_ne_top hC ((ballMaximal_mono volume hf x).trans
    (ballMaximal_const_le volume C (fun x r hr => euclidean_ball_finite_pos x hr) x))

end OAI.Analysis.Fourier.SquareFunction
