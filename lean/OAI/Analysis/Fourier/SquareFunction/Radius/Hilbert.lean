import OAI.Analysis.Fourier.SquareFunction.Shell.Projected
import OAI.Analysis.Fourier.SquareFunction.Shell.L2

/-! The concrete radius Hilbert space on `[1,2]`, with its unnormalized
Lebesgue measure. Continuous radius functions map into it contractively. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

abbrev RadiusInterval := Icc (1 : ℝ) 2

noncomputable def radiusMeasure : Measure RadiusInterval :=
  (volume : Measure ℝ).comap Subtype.val

theorem radiusMeasure_univ : radiusMeasure univ = 1 := by
  let := Measure.Subtype.measureSpace (p := fun r : ℝ => r ∈ Icc (1 : ℝ) 2)
  change (volume : Measure RadiusInterval) univ = 1
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
  norm_num

instance radiusMeasure_isFinite : IsFiniteMeasure radiusMeasure where
  measure_univ_lt_top := by rw [radiusMeasure_univ]; exact ENNReal.one_lt_top

noncomputable abbrev RadiusHilbert := Lp ℂ 2 radiusMeasure

noncomputable def radiusToL2 : C(RadiusInterval, ℂ) →L[ℂ] RadiusHilbert :=
  ContinuousMap.toLp 2 radiusMeasure ℂ

theorem radiusToL2_coe (f : C(RadiusInterval, ℂ)) :
    (radiusToL2 f : RadiusInterval → ℂ) =ᵐ[radiusMeasure] f :=
  ContinuousMap.coeFn_toLp radiusMeasure f

theorem enorm_radiusToL2 (f : C(RadiusInterval, ℂ)) :
    ‖radiusToL2 f‖ₑ = eLpNorm f 2 radiusMeasure := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (radiusToL2_coe f)]

theorem radiusToL2_norm_le : ‖radiusToL2‖ ≤ 1 := by
  have hm : measureUnivNNReal radiusMeasure = 1 := by
    apply ENNReal.coe_injective
    rw [coe_measureUnivNNReal, radiusMeasure_univ]
    rfl
  have h := ContinuousMap.toLp_norm_le (p := (2 : ℝ≥0∞)) (E := ℂ) radiusMeasure (𝕜 := ℂ)
  simpa only [radiusToL2, hm, NNReal.coe_one, Real.one_rpow] using h

theorem norm_radiusToL2_le (f : C(RadiusInterval, ℂ)) : ‖radiusToL2 f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖radiusToL2‖ * ‖f‖ := radiusToL2.le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right radiusToL2_norm_le (norm_nonneg _)
    _ = _ := one_mul _

theorem eLpNorm_radius_restriction (f : ℝ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun r : RadiusInterval => f r) p radiusMeasure =
      eLpNorm f p (volume.restrict (Icc (1 : ℝ) 2)) := by
  have h := (MeasurableEmbedding.subtype_coe measurableSet_Icc).eLpNorm_map_measure
    (g := f) (p := p) (μ := radiusMeasure)
  rw [radiusMeasure, map_comap_subtype_coe measurableSet_Icc] at h
  exact h.symm

theorem enorm_radiusToL2_le_global (f : ℝ → ℂ) (hf : Continuous f) :
    ‖radiusToL2 ⟨fun r : RadiusInterval => f r, hf.comp continuous_subtype_val⟩‖ₑ ≤
      eLpNorm f 2 volume := by
  rw [enorm_radiusToL2]
  change eLpNorm (fun r : RadiusInterval => f r) 2 radiusMeasure ≤ _
  rw [eLpNorm_radius_restriction]
  exact eLpNorm_mono_measure f Measure.restrict_le_self

end OAI.Analysis.Fourier.SquareFunction
