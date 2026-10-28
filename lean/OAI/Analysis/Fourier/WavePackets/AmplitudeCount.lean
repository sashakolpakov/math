import OAI.Analysis.Fourier.WavePackets.Bernstein

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal

/-- Polynomially bounded amplitudes require only logarithmically many
dyadic levels, with the constant uniform in the semiclassical scale. -/
theorem exists_logarithmic_amplitude_count (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ N : ℕ, (N + 1 : ℝ) ≤ D * (1 + Real.log h⁻¹) ∧
        C * (h⁻¹) ^ n < (2 : ℝ) ^ N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogC : 0 ≤ Real.log (C + 1) := Real.log_nonneg (by linarith)
  let a := Real.log (C + 1) / Real.log 2
  let b := (n : ℝ) / Real.log 2
  have ha : 0 ≤ a := div_nonneg hlogC hlog2.le
  have hb : 0 ≤ b := div_nonneg (by positivity) hlog2.le
  refine ⟨a + b + 3, by linarith, ?_⟩
  intro h hh hh1
  have hhi : 0 < h⁻¹ := inv_pos.mpr hh
  have hl : 0 ≤ Real.log h⁻¹ := Real.log_nonneg ((one_le_inv₀ hh).mpr hh1)
  let x := (Real.log (C + 1) + (n : ℝ) * Real.log h⁻¹) / Real.log 2
  have hx : 0 ≤ x := div_nonneg (by positivity) hlog2.le
  let N := ⌈x⌉₊ + 1
  have hround : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have hxexpand : x = a + b * Real.log h⁻¹ := by dsimp [x, a, b]; ring
  refine ⟨N, ?_, ?_⟩
  · have hN : (N + 1 : ℝ) < x + 3 := by
      dsimp [N]
      push_cast
      linarith
    apply hN.le.trans
    rw [hxexpand]
    nlinarith [mul_nonneg ha hl, mul_nonneg hb hl]
  · have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have hxmul : x * Real.log 2 = Real.log (C + 1) + (n : ℝ) * Real.log h⁻¹ :=
      div_mul_cancel₀ _ hlog2.ne'
    have hNlog : Real.log (C + 1) + (n : ℝ) * Real.log h⁻¹ < (N : ℝ) * Real.log 2 := by
      have ht := mul_le_mul_of_nonneg_right hceil hlog2.le
      rw [hxmul] at ht
      dsimp [N]
      push_cast
      nlinarith
    calc
      C * (h⁻¹) ^ n < (C + 1) * (h⁻¹) ^ n :=
        mul_lt_mul_of_pos_right (by linarith) (pow_pos hhi n)
      _ = Real.exp (Real.log (C + 1) + (n : ℝ) * Real.log h⁻¹) := by
        rw [Real.exp_add, Real.exp_log (by linarith : 0 < C + 1),
          Real.exp_nat_mul, Real.exp_log hhi]
      _ < Real.exp ((N : ℝ) * Real.log 2) := Real.exp_lt_exp.mpr hNlog
      _ = (2 : ℝ) ^ N := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

local instance amplitudeCountCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance amplitudeCountCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance amplitudeCountCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Actual annularly projected normalized inputs admit a uniform
logarithmic number of amplitude pieces. -/
theorem periodic_projected_amplitude_count {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ D : ℝ, 0 < D ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ N : ℕ, (N + 1 : ℝ) ≤ D * (1 + Real.log h⁻¹) ∧
        ∀ p : ℝ≥0∞, 1 ≤ p → ∀ f : UnitAddTorus (Fin n) → ℂ,
          Integrable f → eLpNorm f p volume ≤ 1 →
          ∀ x, ‖periodicHalfWave φ h 0 f x‖ < (2 : ℝ) ^ N := by
  obtain ⟨C, hC, hbound⟩ := periodic_coarse_bernstein_normalized hφ hc
  obtain ⟨D, hD, hcount⟩ := exists_logarithmic_amplitude_count n hC.le
  refine ⟨D, hD, ?_⟩
  intro h hh hh1
  obtain ⟨N, hN, hCN⟩ := hcount h hh hh1
  exact ⟨N, hN, fun p hp f hf hfn x => (hbound h hh hh1 p hp f hf hfn 0 x).trans_lt hCN⟩

end OAI.Analysis.Fourier.WavePackets
