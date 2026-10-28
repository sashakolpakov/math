import OAI.Analysis.Fourier.Restriction.Neighborhood
import Mathlib.MeasureTheory.Group.LIntegral

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem lintegral_ball_add {n : ℕ} (F : Space n → ℝ≥0∞) (ω : Space n) (ρ : ℝ) :
    (∫⁻ v in ball (0 : Space n) ρ, F (ω + v)) = ∫⁻ ξ in ball ω ρ, F ξ := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  rw [← lintegral_add_left_eq_self ((ball ω ρ).indicator F) ω]
  apply lintegral_congr
  intro v
  have he : ω + v ∈ ball ω ρ ↔ v ∈ ball (0 : Space n) ρ := by
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  by_cases hv : v ∈ ball (0 : Space n) ρ
  · simp only [indicator_of_mem hv, indicator_of_mem (he.mpr hv)]
  · simp only [indicator_of_notMem hv, indicator_of_notMem (mt he.mp hv)]

theorem sphere_ball_average_identity {n : ℕ} {F : Space n → ℝ≥0∞}
    (hF : Measurable F) (ρ : ℝ) :
    (∫⁻ v in ball (0 : Space n) ρ, ∫⁻ ω, F (ω + v) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      ∫⁻ ξ, F ξ * OAI.Analysis.Fourier.Restriction.sphereMeasure n (ball ξ ρ) := by
  have hm : Measurable (fun z : Space n × Space n ↦ F (z.2 + z.1)) := by fun_prop
  let G : Space n × Space n → ℝ≥0∞ := fun z ↦ (ball z.1 ρ).indicator F z.2
  have hG : Measurable G := by
    have hset : MeasurableSet {z : Space n × Space n | z.2 ∈ ball z.1 ρ} := by
      change MeasurableSet {z : Space n × Space n | dist z.2 z.1 < ρ}
      exact (isOpen_lt (show Continuous (fun z : Space n × Space n ↦ dist z.2 z.1) by fun_prop)
        continuous_const).measurableSet
    exact (hF.comp measurable_snd).indicator hset
  calc
    _ = ∫⁻ ω, ∫⁻ v in ball (0 : Space n) ρ, F (ω + v) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
      lintegral_lintegral_swap (μ := (volume : Measure (Space n)).restrict (ball 0 ρ))
        (ν := OAI.Analysis.Fourier.Restriction.sphereMeasure n) hm.aemeasurable
    _ = ∫⁻ ω, ∫⁻ ξ, G (ω, ξ) ∂volume ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply lintegral_congr
      intro ω
      rw [lintegral_ball_add, ← lintegral_indicator measurableSet_ball]
    _ = ∫⁻ ξ, ∫⁻ ω, G (ω, ξ) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
      lintegral_lintegral_swap (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) (ν := (volume : Measure (Space n))) hG.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro ξ
      have he : (fun ω ↦ G (ω, ξ)) = (ball ξ ρ).indicator (fun _ ↦ F ξ) := by
        funext ω
        dsimp [G]
        have hh : ξ ∈ ball ω ρ ↔ ω ∈ ball ξ ρ := by simp only [mem_ball, dist_comm]
        by_cases hw : ω ∈ ball ξ ρ
        · simp only [indicator_of_mem hw, indicator_of_mem (hh.mpr hw)]
        · simp only [indicator_of_notMem hw, indicator_of_notMem (mt hh.mp hw)]
      rw [he, lintegral_indicator measurableSet_ball, lintegral_const, Measure.restrict_apply_univ]

end OAI.Analysis.Fourier.Restriction
