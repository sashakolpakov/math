import OAI.Analysis.Fourier.WavePackets.Far

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Full Euclidean transfer for the actual half-wave. The hypothesis is
precisely a periodic operator estimate; all Fourier normalization,
periodization, off-cone estimates and cube summation are proved here.
The main coefficient is `11^(n/p) B`, with an arbitrarily small power error. -/
theorem euclidean_bound_of_periodic_bound {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ B : ℝ≥0∞,
      (∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g → MemLp g p volume →
        eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 g q.2)
          p (periodicSpacetimeMeasure n) ≤ B * eLpNorm g p volume) →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, Measurable f → Integrable f → MemLp f p volume →
      eLpNorm (fun q : ℝ × EuclideanSpace ℝ (Fin n) => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2)
        p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) ≤
        (B * ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) + ENNReal.ofReal (C * h ^ N)) * eLpNorm f p volume := by
  obtain ⟨C₁, hC₁, hnear⟩ := nearWave_bound_of_periodic_bound hφ hs hzero N
  obtain ⟨C₂, hC₂, hfar⟩ := farWave_spacetime_bound hφ hs hzero N
  refine ⟨C₁ * 11 ^ n + C₂, add_nonneg (mul_nonneg hC₁ (by positivity)) hC₂, ?_⟩
  intro p hp hptop h hh hh₁ B hper f hm hfi hf
  have ha : ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) ≤ (11 : ℝ≥0∞) ^ n := by
    calc
      _ ≤ ((11 : ℝ≥0∞) ^ n) ^ (1 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
        linarith [one_sub_inv_toReal_nonneg hp]
      _ = _ := ENNReal.rpow_one _
  have herr : ENNReal.ofReal (C₁ * h ^ N) * ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) +
      ENNReal.ofReal (C₂ * h ^ N) ≤ ENNReal.ofReal ((C₁ * 11 ^ n + C₂) * h ^ N) := by
    calc
      _ ≤ ENNReal.ofReal (C₁ * h ^ N) * (11 : ℝ≥0∞) ^ n + ENNReal.ofReal (C₂ * h ^ N) := by gcongr
      _ = _ := by
        rw [show (11 : ℝ≥0∞) ^ n = ENNReal.ofReal ((11 : ℝ) ^ n) by
          rw [ENNReal.ofReal_pow (by norm_num)]; norm_num]
        rw [← ENNReal.ofReal_mul (mul_nonneg hC₁ (pow_nonneg hh.le N)),
          ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hC₁ (pow_nonneg hh.le N)) (by positivity))
            (mul_nonneg hC₂ (pow_nonneg hh.le N))]
        congr 1
        ring
  have heq : (fun q : ℝ × EuclideanSpace ℝ (Fin n) => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) =
      nearWave φ h f + farWave φ h f := by
    funext q
    simp [farWave]
  rw [heq]
  apply (eLpNorm_add_le hp).trans
  apply (add_le_add (hnear p hp hptop h hh hh₁ B hper f hm hf)
    (hfar f hm hfi p hp hptop h hh hh₁)).trans
  calc
    _ = (B * ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) +
        (ENNReal.ofReal (C₁ * h ^ N) * ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) +
          ENNReal.ofReal (C₂ * h ^ N))) * eLpNorm f p volume := by ring
    _ ≤ _ := mul_le_mul' (add_le_add le_rfl herr) le_rfl

end OAI.Analysis.Fourier.WavePackets
