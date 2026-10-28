import OAI.MeasureTheory.Kakeya.CoverVolume
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem maximal_indicator_L1_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture) {n : ℕ} (hn : 2 ≤ n)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ A : Set (Space n),
      MeasurableSet A → volume A ≠ ∞ →
      (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (C * δ ^ (-η)) * volume A ^ (1 / (n : ℝ)) *
          OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ^ (1 - 1 / (n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := hK n hn η hη
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδone A hA hAfin
  have hf : MemLp (A.indicator (fun _ ↦ (1 : ℂ))) n (volume : Measure (Space n)) :=
    memLp_indicator_const _ hA _ (Or.inr hAfin)
  obtain ⟨hKm, hKn⟩ := hbound δ hδ hδone _ hf
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1 : ℝ≥0∞) ≤ n by exact_mod_cast (show 1 ≤ n by omega)) hKm.aestronglyMeasurable
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hninf : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hfNorm : eLpNorm (A.indicator (fun _ ↦ (1 : ℂ))) n (volume : Measure (Space n)) =
      volume A ^ (1 / (n : ℝ)) := by
    rw [eLpNorm_indicator_const hA.nullMeasurableSet hn0 hninf]
    simp
  rw [hfNorm] at hKn
  have hnorm : eLpNorm (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ)))) 1 (OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      ∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
    rw [eLpNorm_one_eq_lintegral_enorm hKm.aestronglyMeasurable]
    simp only [enorm_eq_self]
  rw [hnorm] at hcmp
  simp only [ENNReal.toReal_one, ENNReal.toReal_natCast, div_one] at hcmp
  exact hcmp.trans (mul_le_mul' hKn le_rfl)

end OAI.MeasureTheory.Kakeya
