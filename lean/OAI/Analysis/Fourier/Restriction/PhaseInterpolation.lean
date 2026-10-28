import OAI.Analysis.Fourier.Restriction.PhaseBands
import OAI.Analysis.Fourier.Restriction.DyadicAmplitude
import OAI.Analysis.Fourier.Restriction.BandPowers
import OAI.Analysis.Fourier.BochnerRiesz.FourierLimit

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem finitePhaseSum_congr_on {n : ℕ} (E : Finset (Space n))
    {a b : Space n → ℂ} (hab : ∀ z ∈ E, a z = b z) :
    finitePhaseSum E a = finitePhaseSum E b := by
  funext ξ
  exact Finset.sum_congr rfl (fun z hz ↦ by rw [hab z hz])

theorem finitePhaseSum_sum {n : ℕ} {ι : Type*} (E : Finset (Space n))
    (I : Finset ι) (a : ι → Space n → ℂ) :
    finitePhaseSum E (fun z ↦ ∑ i ∈ I, a i z) =
      fun ξ ↦ ∑ i ∈ I, finitePhaseSum E (a i) ξ := by
  funext ξ
  simp only [finitePhaseSum, Finset.sum_mul]
  exact Finset.sum_comm

theorem finitePhaseSum_low_decomposition {n : ℕ} (E : Finset (Space n))
    (a : Space n → ℂ) (ha : ∀ z ∈ E, ‖a z‖ ≤ 1) (N : ℕ) :
    finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N)) =
      fun ξ ↦ ∑ k ∈ Finset.range N,
        finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)) ξ := by
  rw [← finitePhaseSum_sum]
  apply finitePhaseSum_congr_on
  intro z hz
  rw [amplitudeBand_dyadic_decomposition]
  have H : (∑ k ∈ Finset.range N, amplitudeBand a ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) z) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact amplitudeBand_eq_zero_of_le a _ _ ((ha z hz).trans (one_le_pow₀ (by norm_num)))
  rw [H, zero_add]

/-- Restricted finite exponential-sum bounds improve to strong bounds at
every smaller input exponent, uniformly in the finite set. -/
theorem finitePhaseSum_normalized_bound {n : ℕ} (E : Finset (Space n))
    {p q s : ℝ} (hp : 1 ≤ p) (hq : 0 < q) (hs : 0 ≤ s) (hqs : q * s < 1)
    {C : ℝ≥0∞}
    (hres : ∀ S : Finset (Space n), S ⊆ E → ∀ a : Space n → ℂ,
      (∀ z ∈ S, ‖a z‖ ≤ 1) →
        eLpNorm (finitePhaseSum S a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          C * ENNReal.ofReal ((S.card : ℝ) ^ s))
    (a : Space n → ℂ) (hsum : (∑ z ∈ E, ‖a z‖ ^ q) ≤ 1) :
    eLpNorm (finitePhaseSum E a) (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (C * ENNReal.ofReal ((1 / 2 : ℝ) ^ (-q * s))) *
        ENNReal.ofReal ((1 - (1 / 2 : ℝ) ^ (1 + -q * s))⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have ha : ∀ z ∈ E, ‖a z‖ ≤ 1 :=
    fun z hz ↦ finite_norm_le_one_of_sum_rpow_le_one E a hq hsum hz
  let ρ : ℝ := (1 / 2 : ℝ) ^ (1 + -q * s)
  have hρ : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have Hk (k : ℕ) :
      eLpNorm (finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)))
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      (C * ENNReal.ofReal ((1 / 2 : ℝ) ^ (-q * s))) * ENNReal.ofReal (ρ ^ k) := by
    have H := finitePhaseSum_band_bound E hq hs hres a hsum
      (l := (1 / 2 : ℝ) ^ (k + 1)) (u := (1 / 2 : ℝ) ^ k) (by positivity) (by positivity)
    have he : (1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ (k + 1)) ^ (-q * s) =
        (1 / 2 : ℝ) ^ (-q * s) * ρ ^ k := by
      rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
      rw [show (1 / 2 : ℝ) ^ k * (((1 / 2 : ℝ) ^ k) ^ (-q * s) *
          (1 / 2 : ℝ) ^ (-q * s)) =
        (1 / 2 : ℝ) ^ (-q * s) * ((1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ k) ^ (-q * s)) by ring]
      rw [pow_mul_rpow_band (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [he, ENNReal.ofReal_mul (by positivity)] at H
    simpa only [mul_assoc] using H
  have hlim : ∀ ξ, Tendsto (fun N : ℕ ↦
      finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ N) ((2 : ℝ) ^ N)) ξ)
      atTop (𝓝 (finitePhaseSum E a ξ)) := by
    intro ξ
    exact tendsto_finsetSum E (fun z hz ↦ (tendsto_amplitudeBand a z).mul tendsto_const_nhds)
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_tendsto_pointwise (OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    (fun N ↦ (continuous_finitePhaseSum E _).aestronglyMeasurable)
    (continuous_finitePhaseSum E a).aestronglyMeasurable hlim hp0
  intro N
  rw [finitePhaseSum_low_decomposition E a ha N]
  have hsumNorm : eLpNorm (fun ξ ↦ ∑ k ∈ Finset.range N,
      finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)) ξ)
      (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ∑ k ∈ Finset.range N, eLpNorm
        (finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)))
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    have he : (fun ξ ↦ ∑ k ∈ Finset.range N,
        finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)) ξ) =
        ∑ k ∈ Finset.range N,
          finitePhaseSum E (amplitudeBand a ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)) := by
      funext ξ
      simp only [Finset.sum_apply]
    rw [he]
    exact eLpNorm_sum_le hpE
  exact hsumNorm.trans ((Finset.sum_le_sum (fun k _ ↦ Hk k)).trans
    (sum_mul_ofReal_geometric_le _ (by dsimp [ρ]; positivity) hρ N))

end OAI.Analysis.Fourier.Restriction
