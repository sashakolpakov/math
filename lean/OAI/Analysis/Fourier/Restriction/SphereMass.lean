import OAI.Analysis.Fourier.Restriction.Neighborhood
import OAI.MeasureTheory.Kakeya.Maximal

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sphere_ball_mass_upper {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ∀ x : Space n,
      OAI.Analysis.Fourier.Restriction.sphereMeasure n (ball x ρ) ≤ ENNReal.ofReal (C * ρ ^ (n - 1)) := by
  obtain ⟨c, A, hc, hA, H⟩ := packetCap_real_comparable hn
  let m := (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real univ
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  let C := (A + m + 1) * 64 ^ (n - 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ρ hρ x
  have hcoeff : A ≤ A + m + 1 := by linarith
  have hfull : OAI.Analysis.Fourier.Restriction.sphereMeasure n univ = ENNReal.ofReal m := by
    dsimp [m]
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  by_cases hsmall : 64 * ρ ≤ 1
  · by_cases hex : ∃ v : Space n, ‖v‖ = 1 ∧ dist v x < ρ
    · obtain ⟨v, hv, hvx⟩ := hex
      have hsub : OAI.Analysis.Fourier.Restriction.sphereMeasure n (ball x ρ) ≤ OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap (64 * ρ) v) := by
        apply measure_mono_ae
        filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ω hω
        intro hωx
        refine ⟨hω, ?_⟩
        have ht := dist_triangle ω x v
        have hωx' : dist ω x < ρ := hωx
        rw [dist_comm x v] at ht
        rw [← dist_eq_norm]
        linarith
      have hcap := (H (64 * ρ) v (by positivity) hsmall hv).2
      calc
        _ ≤ OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap (64 * ρ) v) := hsub
        _ = ENNReal.ofReal ((OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap (64 * ρ) v)) := by
          rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ ENNReal.ofReal (A * (64 * ρ) ^ (n - 1)) := ENNReal.ofReal_le_ofReal hcap
        _ ≤ ENNReal.ofReal (C * ρ ^ (n - 1)) := by
          apply ENNReal.ofReal_le_ofReal
          dsimp [C]
          rw [mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
    · have hzero : OAI.Analysis.Fourier.Restriction.sphereMeasure n (ball x ρ) = 0 := by
        have hle : OAI.Analysis.Fourier.Restriction.sphereMeasure n (ball x ρ) ≤ OAI.Analysis.Fourier.Restriction.sphereMeasure n ∅ := by
          apply measure_mono_ae
          filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ω hω
          intro hmem
          exact False.elim (hex ⟨ω, hω, hmem⟩)
        simpa only [measure_empty, nonpos_iff_eq_zero] using hle
      rw [hzero]
      exact bot_le
  · have hone : 1 ≤ (64 * ρ) ^ (n - 1) := one_le_pow₀ (by linarith)
    calc
      _ ≤ OAI.Analysis.Fourier.Restriction.sphereMeasure n univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal m := hfull
      _ ≤ ENNReal.ofReal (C * ρ ^ (n - 1)) := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [C]
        rw [mul_assoc, ← mul_pow]
        calc
          m ≤ A + m + 1 := by linarith
          _ ≤ (A + m + 1) * (64 * ρ) ^ (n - 1) := le_mul_of_one_le_right (by positivity) hone

end OAI.Analysis.Fourier.Restriction
