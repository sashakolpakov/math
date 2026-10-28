import OAI.Analysis.Fourier.Restriction.ThinScale
import OAI.Analysis.Fourier.Restriction.Modulation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The local critical restriction estimate averaged across a thin spherical
annulus. The width contributes its sharp `1/p` power. -/
theorem localSmoothing_thin_annulus (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f → (∀ x, R < ‖x‖ → f x = 0) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (restrictionInputExponent n))
        (volume.restrict (sphericalAnnulus δ)) ≤
      C * ENNReal.ofReal δ ^ (1 / restrictionInputExponent n) * ENNReal.ofReal (R ^ ε) *
        eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume := by
  have hp : 0 < restrictionInputExponent n := lt_trans zero_lt_one (restrictionInputExponent_bounds hn).1
  obtain ⟨A, hA, HA⟩ := thin_annulus_norm_of_translated_sphere_bound (by omega : 1 ≤ n) hp
  obtain ⟨B, hB, HB⟩ := localSmoothing_local_restriction_translated hls hn hε
  refine ⟨A * B, ENNReal.mul_ne_top hA hB, ?_⟩
  intro R hR f hfm hfi hfs δ hδ hδhalf
  have H := HA δ hδ hδhalf (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (continuous_angularFourier hfi).measurable
    (B * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume)
    (HB R hR f hfm hfi hfs)
  convert H using 1 ; ring

end OAI.Analysis.Fourier.Restriction
