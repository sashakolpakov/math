import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.FocusingMoment
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.MomentPowers
import OAI.MeasureTheory.Kakeya.Hausdorff

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped ENNReal

def frequencyMomentExponent (n : ℕ) (p : ℝ) : ℝ :=
  ((n:ℝ)-radialOrder n)*p-1

def timeMomentExponent (n : ℕ) (p : ℝ) : ℝ :=
  ((n-1:ℕ):ℝ)-radialOrder n*p

theorem focusingWave_moment_power_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ p : ℝ, 0 ≤ p → ∃ c : ℝ, 0 < c ∧
      ∀ N : ℝ, 0 < N → ∀ t : ℝ, A/N ≤ t →
      ENNReal.ofReal (c*N^(frequencyMomentExponent n p)*t^(timeMomentExponent n p)) ≤
        ∫⁻ x, ‖focusingWave n N t x‖ₑ^p := by
  obtain ⟨η,k,A,hη,_,hk,hA,h⟩ := focusingWave_spatial_moment_lower hn
  refine ⟨A,hA,fun p hp => ?_⟩
  let s := ((OAI.Analysis.Fourier.Restriction.sphereMeasure n) univ).toReal
  have hspos : 0 < s := ENNReal.toReal_pos (OAI.MeasureTheory.Kakeya.sphereMeasure_univ_pos hn).ne'
    (measure_ne_top _ _)
  have hs : (OAI.Analysis.Fourier.Restriction.sphereMeasure n) univ = ENNReal.ofReal s :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  refine ⟨η*k^p*s,by positivity,fun N hN t ht => ?_⟩
  have ht0 : 0 < t := (div_pos (lt_of_lt_of_le zero_lt_one hA) hN).trans_le ht
  have he := shell_moment_power hN ht0 hk.le η ((n:ℝ)-radialOrder n)
    (-radialOrder n) p ((n-1:ℕ):ℝ)
  have he' : (η/N)*t^(n-1)*s*(k*N^((n:ℝ)-radialOrder n)*t^(-radialOrder n))^p =
      (η*k^p*s)*N^(frequencyMomentExponent n p)*t^(timeMomentExponent n p) := by
    rw [←Real.rpow_natCast t (n-1)]
    dsimp only [frequencyMomentExponent,timeMomentExponent]
    calc
      _ = ((η/N)*t^((n-1:ℕ):ℝ)*(k*N^((n:ℝ)-radialOrder n)*t^(-radialOrder n))^p)*s := by ring
      _ = _ := by rw [he]; simp only [neg_mul,sub_eq_add_neg]; ring
  calc
    _ = ENNReal.ofReal (η/N) * ENNReal.ofReal (t^(n-1)) *
        (OAI.Analysis.Fourier.Restriction.sphereMeasure n) univ *
        (ENNReal.ofReal (k*N^((n:ℝ)-radialOrder n)*t^(-radialOrder n)))^p := by
      rw [hs,ENNReal.ofReal_rpow_of_nonneg (by positivity) hp,
        ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity),
        ←ENNReal.ofReal_mul (by positivity),he']
    _ ≤ _ := h p hp N hN t ht

/-- Exact lower moment from the focusing packet on the actual observation
measure, prior to evaluating its elementary one-dimensional integral. -/
theorem focusing_packet_integrated_moment_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ p : ℝ, 0 ≤ p → ∃ c : ℝ, 0 < c ∧
      ∀ N : ℝ, 0 < N → ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N (3/2) ξ) →
      ENNReal.ofReal (c*N^(frequencyMomentExponent n p)) *
        (∫⁻ t in Icc (A/N) (1/4:ℝ), ENNReal.ofReal (t^(timeMomentExponent n p))) ≤
      ∫⁻ z, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1‖ₑ^p ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n := by
  obtain ⟨A,hA,h⟩ := focusingWave_moment_power_lower hn
  refine ⟨A,hA,fun p hp => ?_⟩
  obtain ⟨c,hc,h⟩ := h p hp
  refine ⟨c,hc,fun N hN f hf => ?_⟩
  calc
    _ = ∫⁻ t in Icc (A/N) (1/4:ℝ),
        ENNReal.ofReal (c*N^(frequencyMomentExponent n p)*t^(timeMomentExponent n p)) := by
      simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ c*N^(frequencyMomentExponent n p))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ t in Icc (A/N) (1/4:ℝ), ∫⁻ x, ‖focusingWave n N t x‖ₑ^p := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact h N hN t ht.1
    _ ≤ _ := focusing_packet_observation_moment hf p (A/N) (1/4)
      (by have : 0 ≤ A/N := div_nonneg (by linarith) hN.le; linarith) (by norm_num)

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
