import OAI.Analysis.PDE.Concentration.NormConversion
import OAI.Analysis.Fourier.WavePackets.Lp

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Fourier.WavePackets
open scoped ENNReal

local instance periodicNormCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance periodicNormCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance periodicNormCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_periodicHalfWave_finite_le {n : ℕ} (s : Finset (Fin n → ℤ))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (hs : ∀ k ∉ s, φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k) = 0)
    (f : UnitAddTorus (Fin n) → ℂ) (t : ℝ) (x : UnitAddTorus (Fin n)) :
    ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h t f x‖ ≤
      ∑ k : s, ‖φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k.val) * UnitAddTorus.mFourierCoeff f k.val‖ := by
  rw [OAI.Analysis.Fourier.WavePackets.periodicHalfWave_eq_finite_sum s φ h hs]
  calc
    _ ≤ ∑ k : s, ‖Complex.exp (-Complex.I * ((t * ‖OAI.Analysis.Fourier.WavePackets.periodicFrequency k.val‖ : ℝ) : ℂ)) *
        (φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k.val) * UnitAddTorus.mFourierCoeff f k.val) *
          UnitAddTorus.mFourier k.val x‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Complex.norm_exp, OAI.Analysis.Fourier.WavePackets.norm_mFourier_apply]

theorem memLp_periodicHalfWave_finite {n : ℕ} (s : Finset (Fin n → ℤ))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (hs : ∀ k ∉ s, φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k) = 0)
    (f : UnitAddTorus (Fin n) → ℂ) (p : ℝ≥0∞) :
    MemLp (fun q : ℝ × UnitAddTorus (Fin n) => OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h q.1 f q.2) p
      (OAI.Analysis.Fourier.WavePackets.periodicSpacetimeMeasure n) := by
  let : IsFiniteMeasure (volume.restrict (Icc (1 : ℝ) 2)) := ⟨by simp⟩
  let : IsFiniteMeasure (OAI.Analysis.Fourier.WavePackets.periodicSpacetimeMeasure n) := by
    unfold OAI.Analysis.Fourier.WavePackets.periodicSpacetimeMeasure
    infer_instance
  apply MemLp.of_bound (OAI.Analysis.Fourier.WavePackets.measurable_periodicHalfWave_spacetime φ h f).aestronglyMeasurable
    (∑ k : s, ‖φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k.val) * UnitAddTorus.mFourierCoeff f k.val‖)
  exact Filter.Eventually.of_forall fun q => norm_periodicHalfWave_finite_le s φ h hs f q.1 q.2

theorem periodicHalfWave_eLpNorm_power {n : ℕ} (s : Finset (Fin n → ℤ))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (hs : ∀ k ∉ s, φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k) = 0)
    (f : UnitAddTorus (Fin n) → ℂ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h q.1 f q.2)
      (.ofReal p) (OAI.Analysis.Fourier.WavePackets.periodicSpacetimeMeasure n) ^ p =
      ENNReal.ofReal (∫ t in (1 : ℝ)..2, ∫ x, ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h t f x‖ ^ p) := by
  have hf := memLp_periodicHalfWave_finite s φ h hs f (.ofReal p)
  rw [eLpNorm_power_eq_ofReal_integral hp hf]
  have hi : Integrable (fun q : ℝ × UnitAddTorus (Fin n) => ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h q.1 f q.2‖ ^ p)
      (OAI.Analysis.Fourier.WavePackets.periodicSpacetimeMeasure n) := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hf.integrable_norm_rpow
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top
  rw [OAI.Analysis.Fourier.WavePackets.periodicSpacetimeMeasure, integral_prod _ hi,
    intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2), integral_Icc_eq_integral_Ioc]

theorem periodic_mixed_bound_ennreal {n : ℕ} (s : Finset (Fin n → ℤ))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (hs : ∀ k ∉ s, φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k) = 0)
    (f : UnitAddTorus (Fin n) → ℂ) {p R : ℝ} (hp : 2 ≤ p) (hR : 0 ≤ R)
    (hb : (∫ t in (1 : ℝ)..2, ∫ x, ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h t f x‖ ^ p) ≤
      R * ‖OAI.Analysis.Fourier.WavePackets.spectralTorusPolynomial s φ h f‖ ^ (p - 2) *
        (∫ x, ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h 0 f x‖ ^ 2)) :
    eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h q.1 f q.2)
      (.ofReal p) (OAI.Analysis.Fourier.WavePackets.periodicSpacetimeMeasure n) ^ p ≤
      ENNReal.ofReal R * (eLpNorm (OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h 0 f) ⊤ volume ^ (p - 2) *
        eLpNorm (OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h 0 f) 2 volume ^ (2 : ℝ)) := by
  rw [periodicHalfWave_eLpNorm_power s φ h hs f (by linarith),
    OAI.Analysis.Fourier.WavePackets.periodicHalfWave_zero_eq_spectralTorusPolynomial s φ h hs f,
    continuousMap_eLpNorm_top, continuousMap_eLpNorm_two_sq,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), ← ENNReal.ofReal_mul hR]
  apply ENNReal.ofReal_le_ofReal
  simpa only [OAI.Analysis.Fourier.WavePackets.periodicHalfWave_zero_eq_spectralTorusPolynomial s φ h hs f, mul_assoc] using hb

end OAI.Analysis.PDE.Concentration
