import OAI.Analysis.Fourier.Restriction.BallAverage

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def sphericalAnnulus {n : ℕ} (δ : ℝ) : Set (Space n) := {x | |‖x‖ - 1| ≤ δ}

theorem measurableSet_sphericalAnnulus {n : ℕ} (δ : ℝ) : MeasurableSet (sphericalAnnulus (n := n) δ) := by
  exact (isClosed_le (show Continuous (fun x : Space n ↦ |‖x‖ - 1|) by fun_prop)
    continuous_const).measurableSet

theorem sphere_thickening_energy {n : ℕ} (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ F : Space n → ℝ≥0∞,
      Measurable F → ENNReal.ofReal (c * δ ^ (n - 1)) * (∫⁻ ξ in sphericalAnnulus δ, F ξ) ≤
        ∫⁻ v in ball (0 : Space n) (2 * δ), ∫⁻ ω, F (ω + v) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  obtain ⟨c, hc, Hc⟩ := sphere_neighborhood_mass_lower hn
  refine ⟨c, hc, ?_⟩
  intro δ hδ hδhalf F hF
  rw [sphere_ball_average_identity hF]
  calc
    _ = ∫⁻ ξ in sphericalAnnulus δ, F ξ * ENNReal.ofReal (c * δ ^ (n - 1)) := by
      rw [lintegral_mul_const'' _ hF.aemeasurable]
      exact mul_comm _ _
    _ ≤ ∫⁻ ξ in sphericalAnnulus δ, F ξ * OAI.Analysis.Fourier.Restriction.sphereMeasure n (ball ξ (2 * δ)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_sphericalAnnulus δ)] with ξ hξ
      exact mul_le_mul' le_rfl (Hc δ hδ hδhalf ξ hξ)
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

end OAI.Analysis.Fourier.Restriction
