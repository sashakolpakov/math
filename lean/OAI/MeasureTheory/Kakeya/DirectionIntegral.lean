import OAI.MeasureTheory.Kakeya.DirectionNets
import OAI.MeasureTheory.Kakeya.MaximalDiscrete
import OAI.MeasureTheory.Kakeya.Maximal

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

theorem packetCap_real_upper_all_scales {n : ℕ} (hn : 1 ≤ n) :
    ∃ U : ℝ, 0 < U ∧ ∀ (δ : ℝ) (v : Space n), 0 < δ → ‖v‖ = 1 →
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ v) ≤ U * δ ^ (n - 1) := by
  obtain ⟨L, C, hL, hC, hcap⟩ := OAI.Analysis.Fourier.Restriction.packetCap_real_comparable hn
  refine ⟨C + (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ, by positivity, ?_⟩
  intro δ v hδ hv
  by_cases hδone : δ ≤ 1
  · exact (hcap δ v hδ hδone hv).2.trans (by
      gcongr
      exact le_add_of_nonneg_right (measureReal_nonneg))
  · have hpow : 1 ≤ δ ^ (n - 1) := one_le_pow₀ (by linarith)
    calc
      _ ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ := measureReal_mono (Set.subset_univ _)
      _ ≤ C + (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ := le_add_of_nonneg_left hC.le
      _ ≤ (C + (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ) * δ ^ (n - 1) :=
        le_mul_of_one_le_right (by positivity) hpow

theorem lintegral_kakeya_le_net {n m : ℕ} {δ p : ℝ} (hδ : 0 < δ) (hp : 0 ≤ p)
    (f : Space n → ℂ) (v : Fin m → Space n)
    (hcover : ∀ ω : Space n, ‖ω‖ = 1 → ∃ i, dist ω (v i) ≤ δ) :
    (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ∑ i, OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap (32 * δ) (v i)) *
        (ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i)) ^ p := by
  let a : Fin m → ℝ≥0∞ := fun i ↦
    (ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i)) ^ p
  let F : Fin m → Space n → ℝ≥0∞ := fun i ↦
    (packetCap (32 * δ) (v i)).indicator (fun _ ↦ a i)
  have hpt : ∀ᵐ ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ p ≤ ∑ i, F i ω := by
    filter_upwards [ae_sphereMeasure_norm n] with ω hω
    obtain ⟨i, hi⟩ := hcover ω hω
    have hmem : ω ∈ packetCap (32 * δ) (v i) := by
      refine ⟨hω, ?_⟩
      simpa only [mul_div_cancel_left₀ δ (by norm_num : (32 : ℝ) ≠ 0), ← dist_eq_norm] using hi
    calc
      _ ≤ a i := ENNReal.rpow_le_rpow (kakeyaMaximal_near_direction hδ f hi) hp
      _ = F i ω := by simp only [F, Set.indicator_of_mem hmem]
      _ ≤ ∑ j, F j ω := Finset.single_le_sum (f := fun j ↦ F j ω)
        (fun j _ ↦ bot_le) (Finset.mem_univ i)
  calc
    _ ≤ ∫⁻ ω, ∑ i, F i ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := lintegral_mono_ae hpt
    _ = ∑ i, OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap (32 * δ) (v i)) * a i := by
      rw [lintegral_finsetSum _ (fun i _ ↦ measurable_const.indicator (measurableSet_packetCap _ _))]
      apply Finset.sum_congr rfl
      intro i _
      simp [lintegral_indicator (measurableSet_packetCap _ _), mul_comm]
    _ = _ := rfl

end OAI.MeasureTheory.Kakeya
