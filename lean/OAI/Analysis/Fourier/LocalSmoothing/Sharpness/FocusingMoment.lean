import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.FocusingLower
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.ShellMeasure
import OAI.Analysis.Fourier.Restriction.ShiftedAnnulus

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped ENNReal

/-- The thin outgoing shell gives a lower bound for the actual spatial
moment. All geometric constants are chosen before the exponent. -/
theorem focusingWave_spatial_moment_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ η k A : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < k ∧ 1 ≤ A ∧
      ∀ p : ℝ, 0 ≤ p → ∀ N : ℝ, 0 < N → ∀ t : ℝ, A/N ≤ t →
      ENNReal.ofReal (η/N) * ENNReal.ofReal (t^(n-1)) *
        (OAI.Analysis.Fourier.Restriction.sphereMeasure n) univ *
        (ENNReal.ofReal (k*N^((n:ℝ)-radialOrder n)*t^(-radialOrder n)))^p ≤
        ∫⁻ x, ‖focusingWave n N t x‖ₑ^p := by
  obtain ⟨η,k,A,hη,hη1,hk,hA,h⟩ := focusingWave_outgoing_lower hn
  refine ⟨η,k,A,hη,hη1,hk,hA,fun p hp N hN t ht => ?_⟩
  have ht0 : 0 < t := (div_pos (lt_of_lt_of_le zero_lt_one hA) hN).trans_le ht
  apply shell_lintegral_lower hn
    (((continuous_focusingWave n hN.ne').comp (continuous_id.prodMk continuous_const)).measurable.enorm.pow_const p)
    ht0 (div_nonneg hη.le hN.le)
  intro x hx hx'
  apply ENNReal.rpow_le_rpow _ hp
  simpa only [ofReal_norm,Function.comp_def,id_eq] using!
    ENNReal.ofReal_le_ofReal (h N hN t ht x hx hx')

/-- A shifted part of the focusing wave is part of the observation interval.
This is an exact comparison for every nonnegative moment. -/
theorem focusing_packet_observation_moment {n : ℕ} {N : ℝ}
    {f : SchwartzMap (Space n) ℂ}
    (hf : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N (3/2) ξ)
    (p a b : ℝ) (ha : -(1/2) ≤ a) (hb : b ≤ 1/2) :
    (∫⁻ t in Icc a b, ∫⁻ x, ‖focusingWave n N t x‖ₑ^p) ≤
      ∫⁻ z, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1‖ₑ^p ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n := by
  have hm := (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).measurable.enorm.pow_const p
  have hs : Measurable (fun t : ℝ => ∫⁻ x, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ^p) :=
    hm.lintegral_prod_left
  have he (t : ℝ) (x : Space n) :
      focusingWave n N t x = OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (t+3/2) f x := by
    simpa only [add_comm] using (focusing_packet_wave hf t x).symm
  simp_rw [he]
  rw [OAI.Analysis.Fourier.Restriction.lintegral_Icc_add_right hs]
  rw [OAI.Analysis.Fourier.LocalSmoothing.observationMeasure, lintegral_prod_symm' _ hm]
  apply lintegral_mono_set
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
