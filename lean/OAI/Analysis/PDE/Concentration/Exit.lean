import OAI.Analysis.PDE.Concentration.Supermean
import OAI.Analysis.Fourier.WavePackets.Cubes

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Filter
open scoped ENNReal

/-- Detection of a time-dependent quantity on an exit boundary, integrated
against an exit measure whose time marginal dominates observation measure.
The boundary energy may be unbounded; no Bochner integrability is assumed. -/
theorem integrated_exit_detection {Ω : Type*} [MeasurableSpace Ω]
    {P ρ : Measure Ω} {μ : Measure ℝ} {T : Ω → ℝ} {g : ℝ → ℝ≥0∞}
    {G : Ω → ℝ≥0∞} {A c E : ℝ≥0∞}
    (hρ : ρ ≤ P) (hT : Measurable T) (hg : Measurable g)
    (hdom : c • μ ≤ Measure.map T ρ)
    (hdetect : ∀ᵐ ω ∂ρ, A * g (T ω) ≤ G ω)
    (hmean : ∫⁻ ω, G ω ∂P ≤ E) :
    A * c * (∫⁻ t, g t ∂μ) ≤ E := by
  calc
    _ = A * (∫⁻ t, g t ∂(c • μ)) := by rw [lintegral_smul_measure]; ac_rfl
    _ ≤ A * (∫⁻ t, g t ∂Measure.map T ρ) :=
      mul_le_mul' le_rfl (lintegral_mono' hdom le_rfl)
    _ = ∫⁻ ω, A * g (T ω) ∂ρ := by
      rw [lintegral_map hg hT]
      simpa only [Function.comp_def] using (lintegral_const_mul A (hg.comp hT)).symm
    _ ≤ ∫⁻ ω, G ω ∂ρ := lintegral_mono_ae hdetect
    _ ≤ ∫⁻ ω, G ω ∂P := lintegral_mono' hρ le_rfl
    _ ≤ E := hmean

/-- The manuscript's `L⁻³` time marginal now gives the corresponding
spacetime estimate from boundary detection and the supermean inequality. -/
theorem integrated_gaussian_exit_detection {Ω : Type*} [MeasurableSpace Ω]
    {P ρ : Measure Ω} {ν : Measure ℝ} {T : Ω → ℝ}
    {g : ℝ → ℝ≥0∞} {G : Ω → ℝ≥0∞} {A E : ℝ≥0∞} {L c : ℝ}
    (hρ : ρ ≤ P) (hT : Measurable T) (hg : Measurable g)
    (hlaw : gaussianExitMixture ν ≤ Measure.map T ρ)
    (hL : 1 ≤ L) (hν : ∀ᵐ s ∂ν, s ∈ Set.Icc 1 (L ^ 2))
    (hmass : ENNReal.ofReal (c / L ^ 2) ≤ ν Set.univ)
    (hdetect : ∀ᵐ ω ∂ρ, A * g (T ω) ≤ G ω)
    (hmean : ∫⁻ ω, G ω ∂P ≤ E) :
    A * ENNReal.ofReal ((Real.exp (-2) / Real.sqrt (2 * Real.pi) * c) / L ^ 3) *
      (∫⁻ t in Set.Icc (1 : ℝ) 2, g t) ≤ E :=
  integrated_exit_detection hρ hT hg
    ((gaussianExitMixture_dominates_cubic hL hν hmass).trans hlaw) hdetect hmean

/-- A nonzero finite detection coefficient yields a genuine finite norm
bound, rather than a vacuous real-valued integral estimate. -/
theorem exit_detection_norm_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u : X → ℂ} {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp_top : p ≠ ∞)
    (hu : Measurable u) {A E : ℝ≥0∞} (hA₀ : A ≠ 0) (hA_top : A ≠ ∞)
    (hbound : A * (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂μ) ≤ E) :
    eLpNorm u p μ ≤ (E / A) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top hu.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow
  · calc
      _ = A⁻¹ * (A * (∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂μ)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hA₀ hA_top, one_mul]
      _ ≤ A⁻¹ * E := mul_le_mul' le_rfl hbound
      _ = E / A := by rw [div_eq_mul_inv, mul_comm]
  · positivity

/-- The boundary energy argument with the actual spacetime `Lp` norm.
The hypotheses separate the probabilistic exit law from the analytic
pointwise energy detection; neither assumes the desired norm estimate. -/
theorem gaussian_exit_spacetime_bound {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {σ : Measure X} [SFinite σ]
    {P ρ : Measure Ω} {ν : Measure ℝ} {T : Ω → ℝ}
    {u : ℝ × X → ℂ} {G : Ω → ℝ≥0∞} {A E : ℝ≥0∞} {L c : ℝ}
    {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp_top : p ≠ ∞)
    (hA₀ : A ≠ 0) (hA_top : A ≠ ∞) (hc : 0 < c)
    (hρ : ρ ≤ P) (hT : Measurable T) (hu : Measurable u)
    (hlaw : gaussianExitMixture ν ≤ Measure.map T ρ)
    (hL : 1 ≤ L) (hν : ∀ᵐ s ∂ν, s ∈ Set.Icc 1 (L ^ 2))
    (hmass : ENNReal.ofReal (c / L ^ 2) ≤ ν Set.univ)
    (hdetect : ∀ᵐ ω ∂ρ, A * (∫⁻ x, ‖u (T ω, x)‖ₑ ^ p.toReal ∂σ) ≤ G ω)
    (hmean : ∫⁻ ω, G ω ∂P ≤ E) :
    eLpNorm u p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod σ) ≤
      (E / (A * ENNReal.ofReal
        ((Real.exp (-2) / Real.sqrt (2 * Real.pi) * c) / L ^ 3))) ^ (1 / p.toReal) := by
  have hm : Measurable (fun q : ℝ × X => ‖u q‖ₑ ^ p.toReal) :=
    hu.enorm.pow_const _
  have hb := integrated_gaussian_exit_detection hρ hT hm.lintegral_prod_right'
    hlaw hL hν hmass hdetect hmean
  have hcoef : 0 < (Real.exp (-2) / Real.sqrt (2 * Real.pi) * c) / L ^ 3 := by
    apply div_pos (mul_pos gaussianDensity_lower_constant_pos hc)
    positivity
  apply exit_detection_norm_bound hp₀ hp_top hu
    (mul_ne_zero hA₀ (ENNReal.ofReal_ne_zero_iff.mpr hcoef))
    (ENNReal.mul_ne_top hA_top ENNReal.ofReal_ne_top)
  rw [lintegral_prod _ hm.aemeasurable]
  exact hb

end OAI.Analysis.PDE.Concentration
