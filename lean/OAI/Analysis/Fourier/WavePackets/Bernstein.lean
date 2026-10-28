import OAI.Analysis.Fourier.WavePackets.AngularGrid
import OAI.Analysis.PDE.Concentration.PeriodicNorm

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set _root_.MeasureTheory OAI.Analysis.PDE.Concentration
open scoped ENNReal

local instance bernsteinCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance bernsteinCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance bernsteinCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def frequencyBox (n M : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(M : ℤ)) (M : ℤ))

theorem card_frequencyBox (n M : ℕ) : (frequencyBox n M).card = (2 * M + 1) ^ n := by
  have he : (M : ℤ) + 1 - -(M : ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
  simp only [frequencyBox, Fintype.card_piFinset, Int.card_Icc, he, Int.toNat_natCast]
  simp

/-- A compact symbol samples at most `O(h⁻ⁿ)` lattice frequencies,
uniformly on the fixed side-100 torus. -/
theorem exists_uniform_frequency_count {n : ℕ} {φ : Space n → ℂ}
    (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ s : Finset (Fin n → ℤ), (s.card : ℝ) ≤ C * (h⁻¹) ^ n ∧
        ∀ k ∉ s, φ (h • periodicFrequency k) = 0 := by
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  let c : ℝ := 2 * Real.pi / 100
  have hc0 : 0 < c := by dsimp [c]; positivity
  let R : ℝ := B / c
  have hR : 0 < R := div_pos hB hc0
  refine ⟨(2 * R + 3) ^ n, by positivity, ?_⟩
  intro h hh hh1
  let M := angularGridSize R h
  refine ⟨frequencyBox n M, ?_, ?_⟩
  · rw [card_frequencyBox, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have ht := angularGrid_card_bound n hR.le hh hh1
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv, mul_pow, M] using ht
  · intro k hk
    by_contra hn
    have hnorm : h * c * ‖integerVector k‖ ≤ B := by
      have hb := hbound _ (subset_tsupport φ hn)
      simpa only [periodicFrequency, norm_smul, Real.norm_eq_abs, abs_of_pos hh,
        abs_of_pos hc0, ← mul_assoc, c] using hb
    have hnorm' : ‖integerVector k‖ ≤ R / h := by
      apply (le_div_iff₀ hh).mpr
      dsimp [R]
      apply (le_div_iff₀ hc0).mpr
      nlinarith
    have hall (i : Fin n) : |((k i : ℤ) : ℝ)| ≤ (M : ℝ) := by
      have hi : |((k i : ℤ) : ℝ)| ≤ ‖integerVector k‖ := by
        simpa only [integerVector, Real.norm_eq_abs] using PiLp.norm_apply_le (integerVector k) i
      exact hi.trans (hnorm'.trans (Nat.le_ceil _))
    apply hk
    simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    constructor
    · exact_mod_cast (abs_le.mp (hall i)).1
    · exact_mod_cast (abs_le.mp (hall i)).2

theorem norm_mFourierCoeff_le_integral {n : ℕ} (f : UnitAddTorus (Fin n) → ℂ)
    (k : Fin n → ℤ) : ‖UnitAddTorus.mFourierCoeff f k‖ ≤ ∫ x, ‖f x‖ := by
  unfold UnitAddTorus.mFourierCoeff
  have ht := norm_integral_le_integral_norm (μ := volume)
    (fun x => UnitAddTorus.mFourier (-k) x • f x)
  simpa only [norm_smul, norm_mFourier_apply, one_mul] using ht

/-- The coarse Bernstein bound sufficient for the logarithmic amplitude
count. Its `h⁻ⁿ` exponent is deliberately nonsharp; no loss is introduced
in the final logarithmic power. -/
theorem periodic_coarse_bernstein {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : UnitAddTorus (Fin n) → ℂ, ∀ t x,
        ‖periodicHalfWave φ h t f x‖ ≤ C * (h⁻¹) ^ n * ∫ y, ‖f y‖ := by
  obtain ⟨C, hC, hcount⟩ := exists_uniform_frequency_count hc
  obtain ⟨B, hφB⟩ := hφ.norm.bddAbove_range_of_hasCompactSupport hc.norm
  let D : ℝ := max 1 B
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hφD (ξ : Space n) : ‖φ ξ‖ ≤ D := (hφB ⟨ξ, rfl⟩).trans (le_max_right _ _)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro h hh hh1 f t x
  obtain ⟨s, hs, hoff⟩ := hcount h hh hh1
  have hfi : 0 ≤ ∫ y, ‖f y‖ := integral_nonneg (fun _ => norm_nonneg _)
  calc
    _ ≤ ∑ k : s, ‖φ (h • periodicFrequency k.val) * UnitAddTorus.mFourierCoeff f k.val‖ :=
      OAI.Analysis.PDE.Concentration.norm_periodicHalfWave_finite_le s φ h hoff f t x
    _ ≤ ∑ _k : s, D * ∫ y, ‖f y‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (hφD _) (norm_mFourierCoeff_le_integral f k.val)
        (norm_nonneg _) hD.le
    _ = (s.card : ℝ) * (D * ∫ y, ‖f y‖) := by simp
    _ ≤ (C * (h⁻¹) ^ n) * (D * ∫ y, ‖f y‖) :=
      mul_le_mul_of_nonneg_right hs (mul_nonneg hD.le hfi)
    _ = (C * D) * (h⁻¹) ^ n * ∫ y, ‖f y‖ := by ring

theorem periodic_coarse_bernstein_normalized {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ p : ℝ≥0∞, 1 ≤ p → ∀ f : UnitAddTorus (Fin n) → ℂ,
        Integrable f → eLpNorm f p volume ≤ 1 → ∀ t x,
          ‖periodicHalfWave φ h t f x‖ ≤ C * (h⁻¹) ^ n := by
  obtain ⟨C, hC, hbound⟩ := periodic_coarse_bernstein hφ hc
  refine ⟨C, hC, ?_⟩
  intro h hh hh1 p hp f hf hfn t x
  have hL1 : ENNReal.ofReal (∫ y, ‖f y‖) ≤ 1 := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hf,
      ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact (eLpNorm_le_eLpNorm_of_exponent_le hp).trans hfn
  have hL1' : (∫ y, ‖f y‖) ≤ 1 := by exact_mod_cast hL1
  exact (hbound h hh hh1 f t x).trans
    (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hL1'
      (show 0 ≤ C * (h⁻¹) ^ n by positivity)))

end OAI.Analysis.Fourier.WavePackets
