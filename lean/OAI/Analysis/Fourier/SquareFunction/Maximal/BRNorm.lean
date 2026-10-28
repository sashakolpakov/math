import OAI.Analysis.Fourier.SquareFunction.Maximal.BREnvelope

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction


theorem eLpNorm_brMaximalShellEnvelope_le {n : ℕ} {p δ σ K C D : ℝ}
    (hp : 1 < p) (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgap : σ < δ) (J : ℕ)
    (hmax : ∀ G : Space n → ℝ≥0∞, Measurable G → (∀ x, G x ≠ ⊤) →
      eLpNorm (ballMaximal volume G) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal D * eLpNorm G (ENNReal.ofReal p) volume)
    (f : SchwartzMap (Space n) ℂ)
    (hshell : ∀ j, eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.maximalShellCycles (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ) ((2 : ℝ) ^ (J + j)) f)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ (J + j)) ^ σ) *
        eLpNorm f (ENNReal.ofReal p) volume) :
    eLpNorm (brMaximalShellEnvelope δ K J f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((K * D * C) * (1 - (2 : ℝ) ^ (σ - δ))⁻¹) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  apply eLpNorm_dyadic_envelope_sum_le volume
    (fun j => ((measurable_ballMaximal volume _).const_mul _).const_mul _)
    hp.le (by positivity) hgap J (eLpNorm f (ENNReal.ofReal p) volume)
  intro j
  rw [eLpNorm_ennreal_const_mul volume ((measurable_ballMaximal volume _).const_mul _) _
      (by linarith), eLpNorm_ennreal_const_mul volume (measurable_ballMaximal volume _) _
      (by linarith)]
  apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl
    ((hmax _ (OAI.Analysis.Fourier.BochnerRiesz.measurable_maximalShellCycles _ _ f) (maximalShellCycles_ne_top _ _ f)).trans
      (mul_le_mul' le_rfl (hshell j))))).trans_eq
  simp only [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ ((2 : ℝ) ^ (J + j)) ^ (-δ)),
    ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hD]
  congr 2
  ring

theorem eLpNorm_brMaximalInteriorEnvelope_le {n : ℕ} {p B D : ℝ}
    (hp : 1 < p) (hB : 0 ≤ B)
    (hmax : ∀ G : Space n → ℝ≥0∞, Measurable G → (∀ x, G x ≠ ⊤) →
      eLpNorm (ballMaximal volume G) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal D * eLpNorm G (ENNReal.ofReal p) volume)
    (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (fun x => ENNReal.ofReal B * ballMaximal volume (fun y => ‖f y‖ₑ) x)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (B * D) * eLpNorm f (ENNReal.ofReal p) volume := by
  rw [eLpNorm_ennreal_const_mul volume (measurable_ballMaximal volume _) _ (by linarith)]
  apply (mul_le_mul' le_rfl (hmax _ f.continuous.measurable.enorm
    (fun x => enorm_ne_top))).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul hB]
  congr 1
  apply eLpNorm_congr_enorm_ae f.continuous.measurable.enorm.aestronglyMeasurable
    f.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => enorm_eq_self _)

end OAI.Analysis.Fourier.SquareFunction
