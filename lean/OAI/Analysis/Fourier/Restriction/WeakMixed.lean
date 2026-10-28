import OAI.Analysis.Fourier.Restriction.Basic
import OAI.Analysis.Fourier.Restriction.Markov
import OAI.Analysis.Fourier.Restriction.TruncationMoments

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem sphericalExtension_add {n : ℕ} {f g : Space n → ℂ}
    (hf : Integrable f (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) (hg : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ f ω + g ω) x = OAI.Analysis.Fourier.Restriction.sphericalExtension f x + OAI.Analysis.Fourier.Restriction.sphericalExtension g x := by
  simp only [OAI.Analysis.Fourier.Restriction.sphericalExtension, mul_add]
  exact integral_add (spherical_integrand_integrable hf x) (spherical_integrand_integrable hg x)

/-- Normalized weak mixed-range estimate from a single diagonal
extension estimate. Its proof uses a genuine high/low amplitude split,
not an assumed interpolation theorem. -/
theorem sphericalExtension_weak_mixed_parameter {n : ℕ} {a s : ℝ}
    (ha : 1 < a) (has : a ≤ s) {C : ℝ≥0∞}
    (hdiag : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal s) volume ≤
        C * eLpNorm g (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {g : Space n → ℂ} (hgm : Measurable g) (hgi : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    (hgn : (∫⁻ ω, ‖g ω‖ₑ ^ a ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ 1)
    {τ : ℝ} (hτ : 0 < τ) :
    volume {x | 2 * τ ^ (1 - a) < ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖} ≤
      (C ^ s * ENNReal.ofReal (τ ^ (s - a))) / ENNReal.ofReal (τ ^ (1 - a)) ^ s := by
  have hs : 0 < s := by linarith
  have hL : 0 < τ ^ (1 - a) := Real.rpow_pos_of_pos hτ _
  have hhi := integrable_amplitudeHigh hgm hgi τ
  have hlo := integrable_amplitudeLow hgm hgi τ
  have hlowMeas : AEStronglyMeasurable (amplitudeLow g τ) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := hlo.aestronglyMeasurable
  have hlowLp : MemLp (amplitudeLow g τ) (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    MemLp.of_enorm_bound hlowMeas ENNReal.ofReal_ne_top
      (Filter.Eventually.of_forall (enorm_amplitudeLow_le g hτ.le))
  have hhighBound (x : Space n) : ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (amplitudeHigh g τ) x‖ ≤ τ ^ (1 - a) := by
    have H : ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (amplitudeHigh g τ) x‖ₑ ≤ ENNReal.ofReal (τ ^ (1 - a)) := by
      calc
        _ ≤ ∫⁻ ω, ‖amplitudeHigh g τ ω‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := enorm_sphericalExtension_le _ _
        _ ≤ ENNReal.ofReal (τ ^ (1 - a)) * ∫⁻ ω, ‖g ω‖ₑ ^ a ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
          lintegral_amplitudeHigh_le_moment (OAI.Analysis.Fourier.Restriction.sphereMeasure n) hgm hτ ha.le
        _ ≤ ENNReal.ofReal (τ ^ (1 - a)) * 1 := by gcongr
        _ = _ := mul_one _
    exact (ENNReal.ofReal_le_ofReal_iff hL.le).mp (by simpa only [ofReal_norm] using H)
  have hlowMoment : (∫⁻ ω, ‖amplitudeLow g τ ω‖ₑ ^ s ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (τ ^ (s - a)) := by
    calc
      _ ≤ ENNReal.ofReal (τ ^ (s - a)) * ∫⁻ ω, ‖g ω‖ₑ ^ a ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
        lintegral_amplitudeLow_le_moment (OAI.Analysis.Fourier.Restriction.sphereMeasure n) hgm hτ.le (by linarith) has
      _ ≤ ENNReal.ofReal (τ ^ (s - a)) * 1 := by gcongr
      _ = _ := mul_one _
  have hELow : AEStronglyMeasurable (OAI.Analysis.Fourier.Restriction.sphericalExtension (amplitudeLow g τ)) volume :=
    (continuous_sphericalExtension hlo).aestronglyMeasurable
  have hELowMoment : (∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (amplitudeLow g τ) x‖ₑ ^ s) ≤
      C ^ s * ENNReal.ofReal (τ ^ (s - a)) := by
    rw [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hs hELow]
    calc
      _ ≤ (C * eLpNorm (amplitudeLow g τ) (ENNReal.ofReal s) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) ^ s :=
        ENNReal.rpow_le_rpow (hdiag _ hlowLp) hs.le
      _ = C ^ s * ∫⁻ ω, ‖amplitudeLow g τ ω‖ₑ ^ s ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le, OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hs hlowMeas]
      _ ≤ _ := mul_le_mul le_rfl hlowMoment zero_le zero_le
  calc
    _ ≤ volume {x | τ ^ (1 - a) < ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (amplitudeLow g τ) x‖} := by
      apply measure_mono
      intro x hx
      have he := sphericalExtension_add hhi hlo x
      rw [amplitudeHigh_add_low] at he
      have hn : ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ ≤
          ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (amplitudeHigh g τ) x‖ + ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (amplitudeLow g τ) x‖ := by
        rw [he]
        exact norm_add_le _ _
      have hh := hhighBound x
      change τ ^ (1 - a) < _
      change 2 * τ ^ (1 - a) < ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ at hx
      linarith
    _ ≤ (∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (amplitudeLow g τ) x‖ₑ ^ s) /
        ENNReal.ofReal (τ ^ (1 - a)) ^ s :=
      measure_norm_gt_le_moment volume (continuous_sphericalExtension hlo).measurable hs hL
    _ ≤ _ := by gcongr

end OAI.Analysis.Fourier.Restriction
