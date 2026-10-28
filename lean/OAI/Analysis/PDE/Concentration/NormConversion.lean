import OAI.Analysis.PDE.Concentration.ProjectedSector

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory
open scoped ENNReal

theorem continuousMap_eLpNorm_top {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [Measure.IsOpenPosMeasure μ]
    (f : C(X, ℂ)) : eLpNorm f ⊤ μ = ENNReal.ofReal ‖f‖ := by
  have hu : eLpNorm f ⊤ μ ≤ ENNReal.ofReal ‖f‖ := by
    rw [eLpNorm_exponent_top f.continuous.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound
      (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
  have ht : eLpNorm f ⊤ μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have ha : ∀ᵐ x ∂μ, ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal := by
    have hb := enorm_ae_le_eLpNormEssSup f μ
    rw [← eLpNorm_exponent_top f.continuous.aestronglyMeasurable] at hb
    filter_upwards [hb] with x hx
    simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm] using ENNReal.toReal_mono ht hx
  have hd := Measure.dense_of_ae ha
  have hc : IsClosed {x | ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal} :=
    isClosed_le f.continuous.norm continuous_const
  have he : {x | ‖f x‖ ≤ (eLpNorm f ⊤ μ).toReal} = univ := hc.closure_eq.symm.trans hd.closure_eq
  have hn : ‖f‖ ≤ (eLpNorm f ⊤ μ).toReal :=
    (ContinuousMap.norm_le f ENNReal.toReal_nonneg).mpr (Set.eq_univ_iff_forall.mp he)
  apply le_antisymm hu
  calc
    ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal (eLpNorm f ⊤ μ).toReal := ENNReal.ofReal_le_ofReal hn
    _ = _ := ENNReal.ofReal_toReal ht

theorem eLpNorm_power_eq_ofReal_integral {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ENNReal.ofReal (∫ x, ‖f x‖ ^ p ∂μ) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal hp.le]
  have hi : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ := integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hi _) hp.le,
    ← Real.rpow_mul hi, inv_mul_cancel₀ hp.ne', Real.rpow_one]

theorem continuousMap_eLpNorm_two_sq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℂ)) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  have hf : MemLp f (ENNReal.ofReal 2) μ := MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
  simpa only [ENNReal.ofReal_ofNat, Real.rpow_ofNat] using
    eLpNorm_power_eq_ofReal_integral (by norm_num : (0 : ℝ) < 2) hf

end OAI.Analysis.PDE.Concentration
