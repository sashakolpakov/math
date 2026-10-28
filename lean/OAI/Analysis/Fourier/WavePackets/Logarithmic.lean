import OAI.Analysis.Fourier.WavePackets.Euclidean

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The periodic logarithmic estimate, stated separately so that the transfer
theorem does not misrepresent this still independent analytic proposition as proved. -/
def PeriodicLogarithmicRefinement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ φ : EuclideanSpace ℝ (Fin n) → ℂ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ → 0 ∉ tsupport φ →
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ g : UnitAddTorus (Fin n) → ℂ, Measurable g →
      MemLp g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume →
      eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 g q.2)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (periodicSpacetimeMeasure n) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm g (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume

theorem one_le_criticalExponent {n : ℕ} (hn : 2 ≤ n) : 1 ≤ OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  apply (le_div_iff₀ (by linarith)).mpr
  linarith

/-- The exact `LogarithmicRefinement` target follows from the periodic
logarithmic estimate. This supplies the complete analytic removal of period,
including product-measure order and finite output norms. -/
theorem logarithmicRefinement_of_periodic (hperiodic : PeriodicLogarithmicRefinement) :
    OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement := by
  intro n hn φ hφ hs hzero
  obtain ⟨C₀, hC₀, hb₀⟩ := hperiodic n hn φ hφ hs hzero
  obtain ⟨C₁, hC₁, hb₁⟩ := euclidean_bound_of_periodic_bound hφ hs hzero 0
  let C := C₀ * 11 ^ n + C₁ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro h hh hh₁ f
  let p := ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)
  have hp : 1 ≤ p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (one_le_criticalExponent hn)
  have hptop : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have he := hb₁ p hp hptop h hh hh₁
    (ENNReal.ofReal (C₀ * (1 + Real.log (1 / h)) ^ (2 * n + 5)))
    (hb₀ h hh hh₁) f f.continuous.measurable f.integrable (f.memLp p volume)
  simp only [pow_zero, mul_one] at he
  have ha : ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) ≤ (11 : ℝ≥0∞) ^ n := by
    calc
      _ ≤ ((11 : ℝ≥0∞) ^ n) ^ (1 : ℝ) := by
        apply ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
        linarith [one_sub_inv_toReal_nonneg hp]
      _ = _ := ENNReal.rpow_one _
  have hlog : 0 ≤ Real.log (1 / h) := Real.log_nonneg ((le_div_iff₀ hh).mpr (by simpa using hh₁))
  have hpow : 1 ≤ (1 + Real.log (1 / h)) ^ (2 * n + 5) := one_le_pow₀ (by linarith)
  have hcoef : ENNReal.ofReal (C₀ * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
      ((11 : ℝ≥0∞) ^ n) ^ (1 / p.toReal) + ENNReal.ofReal C₁ ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) := by
    calc
      _ ≤ ENNReal.ofReal (C₀ * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
          (11 : ℝ≥0∞) ^ n + ENNReal.ofReal C₁ := by gcongr
      _ = ENNReal.ofReal (C₀ * (1 + Real.log (1 / h)) ^ (2 * n + 5) * 11 ^ n + C₁) := by
        rw [show (11 : ℝ≥0∞) ^ n = ENNReal.ofReal ((11 : ℝ) ^ n) by
          rw [ENNReal.ofReal_pow (by norm_num)]; norm_num]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) hC₁]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [C]
        nlinarith [mul_nonneg hC₁ (sub_nonneg.mpr hpow)]
  have hnorm : eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
      p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) * eLpNorm f p volume := by
    have hm := measurable_frequencyHalfWave_spacetime hφ.continuous hs hh f.continuous.measurable f.integrable
    have hswap := eLpNorm_comp_measurePreserving (p := p) hm.aestronglyMeasurable
      (Measure.measurePreserving_swap (μ := (volume : Measure (Space n)))
        (ν := volume.restrict (Set.Icc (1 : ℝ) 2)))
    change eLpNorm ((fun q : ℝ × Space n => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) ∘ Prod.swap)
      p (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) ≤ _
    rw [hswap]
    exact he.trans (mul_le_mul' hcoef le_rfl)
  refine ⟨?_, hnorm⟩
  exact hnorm.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp p volume).eLpNorm_lt_top)

end OAI.Analysis.Fourier.WavePackets
