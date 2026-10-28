import OAI.Analysis.Fourier.WavePackets.NormalizedCritical
import OAI.Analysis.Fourier.WavePackets.Homogeneity
import OAI.Analysis.Fourier.WavePackets.Logarithmic

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal ContDiff

local instance allScalesCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance allScalesCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance allScalesCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem periodicSpacetimeMeasure_univ (n : ℕ) : periodicSpacetimeMeasure n Set.univ = 1 := by
  norm_num [periodicSpacetimeMeasure, Measure.prod_apply, Real.volume_Icc]

/-- The bounded range of semiclassical scales is absorbed into the constant;
the logarithmic loss comes only from the small-scale argument. -/
theorem normalized_periodic_all_scales_of_packet_solvability {n : ℕ}
    (hsolve : PositivePacketSolvability n) {φ : Space (n + 2) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : UnitAddTorus (Fin (n + 2)) → ℂ, Measurable f → Integrable f →
        eLpNorm f (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2))) volume ≤ 1 →
        eLpNorm (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => periodicHalfWave φ h q.1 f q.2)
          (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2))) (periodicSpacetimeMeasure (n + 2)) ≤
            ENNReal.ofReal (C * (1 + Real.log h⁻¹) ^ (2 * (n + 2) + 5)) := by
  obtain ⟨Cs, h₀, hCs, hh₀, hh₀1, hsmall⟩ :=
    normalized_periodic_critical_of_packet_solvability hsolve hφ hc hz
  obtain ⟨Cb, hCb, hlarge⟩ := periodic_coarse_bernstein_normalized hφ.continuous hc
  let B := Cb * (h₀⁻¹) ^ (n + 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨Cs + B, by linarith, ?_⟩
  intro h hh hh1 f hf hfi hfn
  have hlog : 1 ≤ 1 + Real.log h⁻¹ := by
    have := Real.log_nonneg ((one_le_inv₀ hh).mpr hh1)
    linarith
  have hpow : 1 ≤ (1 + Real.log h⁻¹) ^ (2 * (n + 2) + 5) := one_le_pow₀ hlog
  by_cases hhs : h ≤ h₀
  · have hp : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2) = 2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
      unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
      push_cast
      ring
    rw [hp] at hfn ⊢
    exact (hsmall h hh hhs f hf hfi hfn).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))
  · have hp : (1 : ℝ≥0∞) ≤ .ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2)) := by
      simpa using ENNReal.ofReal_le_ofReal (one_le_criticalExponent (n := n + 2) (by omega))
    have hpoint (q : ℝ × UnitAddTorus (Fin (n + 2))) :
        ‖periodicHalfWave φ h q.1 f q.2‖ ≤ B := by
      apply (hlarge h hh hh1 _ hp f hfi hfn q.1 q.2).trans
      apply mul_le_mul_of_nonneg_left _ hCb.le
      exact pow_le_pow_left₀ (by positivity) ((inv_le_inv₀ hh hh₀).mpr (le_of_not_ge hhs)) _
    have hout := eLpNorm_le_of_ae_bound
      (p := ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2)))
      (μ := periodicSpacetimeMeasure (n + 2))
      (measurable_periodicHalfWave_spacetime φ h f).aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
    rw [periodicSpacetimeMeasure_univ, ENNReal.one_rpow, one_mul] at hout
    apply hout.trans (ENNReal.ofReal_le_ofReal _)
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hpow)]

/-- The full periodic critical theorem: no input normalization and no
small-scale restriction remain. Its sole analytic hypothesis is existence
of the concrete admissible packet Dirichlet solutions. -/
theorem periodic_critical_of_packet_solvability {n : ℕ}
    (hsolve : PositivePacketSolvability n) {φ : Space (n + 2) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : UnitAddTorus (Fin (n + 2)) → ℂ, Measurable f →
        MemLp f (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2))) volume →
        eLpNorm (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => periodicHalfWave φ h q.1 f q.2)
          (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2))) (periodicSpacetimeMeasure (n + 2)) ≤
            ENNReal.ofReal (C * (1 + Real.log h⁻¹) ^ (2 * (n + 2) + 5)) *
              eLpNorm f (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2))) volume := by
  obtain ⟨C, hC, hbound⟩ := normalized_periodic_all_scales_of_packet_solvability hsolve hφ hc hz
  refine ⟨C, hC, ?_⟩
  intro h hh hh1 f hf hfp
  have hp : (1 : ℝ≥0∞) ≤ .ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent (n + 2)) := by
    simpa using ENNReal.ofReal_le_ofReal (one_le_criticalExponent (n := n + 2) (by omega))
  exact periodic_bound_of_normalized φ h _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hp))
    (hbound h hh hh1) f hf (hfp.integrable hp) hfp

theorem periodicLogarithmicRefinement_of_packet_solvability
    (hsolve : ∀ n : ℕ, PositivePacketSolvability n) : PeriodicLogarithmicRefinement := by
  intro N hN φ hφ hc hz
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  simpa only [one_div] using periodic_critical_of_packet_solvability (hsolve n) hφ hc hz

/-- Exact Euclidean logarithmic refinement reduced solely to the packet
Dirichlet existence theorem. All transfer, concentration, angular, and
amplitude estimates are proved. -/
theorem logarithmicRefinement_of_packet_solvability
    (hsolve : ∀ n : ℕ, PositivePacketSolvability n) : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement :=
  logarithmicRefinement_of_periodic (periodicLogarithmicRefinement_of_packet_solvability hsolve)

end OAI.Analysis.Fourier.WavePackets
