import OAI.Analysis.Fourier.Cone.InterpolationOperator

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone.FiniteExtension

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} {T : FiniteExtension μ ν}

theorem weak_mixed_parameter {a s : ℝ}
    (ha : 1 < a) (has : a ≤ s) {C : ℝ≥0∞}
    (hdiag : ∀ g : X → ℂ, MemLp g (ENNReal.ofReal s) μ →
      eLpNorm (T g) (ENNReal.ofReal s) ν ≤
        C * eLpNorm g (ENNReal.ofReal s) μ)
    {g : X → ℂ} (hgm : Measurable g) (hgi : Integrable g μ)
    (hgn : (∫⁻ ω, ‖g ω‖ₑ ^ a ∂μ) ≤ 1)
    {τ : ℝ} (hτ : 0 < τ) :
    ν {x | 2 * τ ^ (1 - a) < ‖T g x‖} ≤
      (C ^ s * ENNReal.ofReal (τ ^ (s - a))) / ENNReal.ofReal (τ ^ (1 - a)) ^ s := by
  have hs : 0 < s := by linarith
  have hL : 0 < τ ^ (1 - a) := Real.rpow_pos_of_pos hτ _
  have hhi := OAI.Analysis.Fourier.Restriction.integrable_amplitudeHigh hgm hgi τ
  have hlo := OAI.Analysis.Fourier.Restriction.integrable_amplitudeLow hgm hgi τ
  have hlowMeas : AEStronglyMeasurable (OAI.Analysis.Fourier.Restriction.amplitudeLow g τ) μ := hlo.aestronglyMeasurable
  have hlowLp : MemLp (OAI.Analysis.Fourier.Restriction.amplitudeLow g τ) (ENNReal.ofReal s) μ :=
    MemLp.of_enorm_bound hlowMeas ENNReal.ofReal_ne_top
      (Filter.Eventually.of_forall (OAI.Analysis.Fourier.Restriction.enorm_amplitudeLow_le g hτ.le))
  have hhighBound (x : Y) : ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh g τ) x‖ ≤ τ ^ (1 - a) := by
    have H : ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh g τ) x‖ₑ ≤ ENNReal.ofReal (τ ^ (1 - a)) := by
      calc
        _ ≤ ∫⁻ ω, ‖OAI.Analysis.Fourier.Restriction.amplitudeHigh g τ ω‖ₑ ∂μ := T.bound _ _
        _ ≤ ENNReal.ofReal (τ ^ (1 - a)) * ∫⁻ ω, ‖g ω‖ₑ ^ a ∂μ :=
          OAI.Analysis.Fourier.Restriction.lintegral_amplitudeHigh_le_moment μ hgm hτ ha.le
        _ ≤ ENNReal.ofReal (τ ^ (1 - a)) * 1 := by gcongr
        _ = _ := mul_one _
    exact (ENNReal.ofReal_le_ofReal_iff hL.le).mp (by simpa only [ofReal_norm] using H)
  have hlowMoment : (∫⁻ ω, ‖OAI.Analysis.Fourier.Restriction.amplitudeLow g τ ω‖ₑ ^ s ∂μ) ≤
      ENNReal.ofReal (τ ^ (s - a)) := by
    calc
      _ ≤ ENNReal.ofReal (τ ^ (s - a)) * ∫⁻ ω, ‖g ω‖ₑ ^ a ∂μ :=
        OAI.Analysis.Fourier.Restriction.lintegral_amplitudeLow_le_moment μ hgm hτ.le (by linarith) has
      _ ≤ ENNReal.ofReal (τ ^ (s - a)) * 1 := by gcongr
      _ = _ := mul_one _
  have hELow : AEStronglyMeasurable (T (OAI.Analysis.Fourier.Restriction.amplitudeLow g τ)) ν :=
    (T.measurable _ hlo).aestronglyMeasurable
  have hELowMoment : (∫⁻ x, ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow g τ) x‖ₑ ^ s ∂ν) ≤
      C ^ s * ENNReal.ofReal (τ ^ (s - a)) := by
    rw [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hs hELow]
    calc
      _ ≤ (C * eLpNorm (OAI.Analysis.Fourier.Restriction.amplitudeLow g τ) (ENNReal.ofReal s) μ) ^ s :=
        ENNReal.rpow_le_rpow (hdiag _ hlowLp) hs.le
      _ = C ^ s * ∫⁻ ω, ‖OAI.Analysis.Fourier.Restriction.amplitudeLow g τ ω‖ₑ ^ s ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le, OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hs hlowMeas]
      _ ≤ _ := mul_le_mul le_rfl hlowMoment zero_le zero_le
  calc
    _ ≤ ν {x | τ ^ (1 - a) < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow g τ) x‖} := by
      apply measure_mono
      intro x hx
      have he := T.map_add _ _ hhi hlo x
      rw [OAI.Analysis.Fourier.Restriction.amplitudeHigh_add_low] at he
      have hn : ‖T g x‖ ≤
          ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh g τ) x‖ + ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow g τ) x‖ := by
        rw [he]
        exact norm_add_le _ _
      have hh := hhighBound x
      change τ ^ (1 - a) < _
      change 2 * τ ^ (1 - a) < ‖T g x‖ at hx
      linarith
    _ ≤ (∫⁻ x, ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow g τ) x‖ₑ ^ s ∂ν) /
        ENNReal.ofReal (τ ^ (1 - a)) ^ s :=
      OAI.Analysis.Fourier.Restriction.measure_norm_gt_le_moment ν (T.measurable _ hlo) hs hL
    _ ≤ _ := by gcongr

end OAI.Analysis.Fourier.Cone.FiniteExtension
