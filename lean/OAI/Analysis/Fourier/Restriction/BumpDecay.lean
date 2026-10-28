import OAI.Analysis.Fourier.Restriction.FourierBump

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem translatedFrequencyBump_product_decay {n : ℕ} (hn : 1 ≤ n)
    (f g : SchwartzMap (Space n) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ v w x : Space n,
      ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump f R v) ω *
        OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump g R w) ω) x‖ ≤
      C * (R ^ n * R ^ (((n : ℝ) - 1) / 2)) ^ 2 * (1 + ‖x‖) ^ (-((n : ℝ) - 1) / 2) := by
  obtain ⟨C, hC, HC⟩ := sphericalExtension_fourier_product_decay hn
  let a : ℝ := ((n : ℝ) - 1) / 2
  have ha : 0 ≤ a := by
    dsimp [a]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let If : ℝ := ∫ y : Space n, ‖f y‖ * (1 + ‖y‖) ^ a
  let Ig : ℝ := ∫ y : Space n, ‖g y‖ * (1 + ‖y‖) ^ a
  have hIf : 0 ≤ If := by dsimp [If]; positivity
  have hIg : 0 ≤ Ig := by dsimp [Ig]; positivity
  refine ⟨C * If * Ig, by positivity, ?_⟩
  intro R hR v w x
  have hR0 : 0 < R := by linarith
  obtain ⟨hfi, hf⟩ := translatedFrequencyBump_weight_bound f hR ha v
  obtain ⟨hgi, hg⟩ := translatedFrequencyBump_weight_bound g hR ha w
  have H := HC _ _ (integrable_translatedFrequencyBump f.integrable hR0 v)
    (integrable_translatedFrequencyBump g.integrable hR0 w) hfi hgi x
  apply H.trans
  have hIfR : 0 ≤ ∫ y, ‖translatedFrequencyBump f R v y‖ * (1 + ‖y‖) ^ a := by positivity
  have hIgR : 0 ≤ ∫ y, ‖translatedFrequencyBump g R w y‖ * (1 + ‖y‖) ^ a := by positivity
  simp only [neg_div]
  change C * (∫ y, ‖translatedFrequencyBump f R v y‖ * (1 + ‖y‖) ^ a) *
      (∫ y, ‖translatedFrequencyBump g R w y‖ * (1 + ‖y‖) ^ a) * (1 + ‖x‖) ^ (-a) ≤ _
  calc
    _ ≤ C * ((R ^ n * R ^ a) * If) * ((R ^ n * R ^ a) * Ig) * (1 + ‖x‖) ^ (-a) := by
      gcongr
    _ = _ := by dsimp [a]; ring

end OAI.Analysis.Fourier.Restriction
