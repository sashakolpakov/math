import OAI.Analysis.Fourier.Cone.InterpolationNormalized

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone.FiniteExtension

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} {T : FiniteExtension μ ν}

theorem mixed_of_measurable {a s b : ℝ}
    (ha : 1 < a) (has : a ≤ s) (hb : 0 < b)
    (hab : a * (s - 1) / (a - 1) < b) {C : ℝ≥0∞}
    (hdiag : ∀ g : X → ℂ, MemLp g (ENNReal.ofReal s) μ →
      eLpNorm (T g) (ENNReal.ofReal s) ν ≤
        C * eLpNorm g (ENNReal.ofReal s) μ)
    {g : X → ℂ} (hgm : Measurable g)
    (hga : MemLp g (ENNReal.ofReal a) μ) :
    eLpNorm (T g) (ENNReal.ofReal b) ν ≤
      FiniteExtension.mixedExtensionConstant μ a s b C * eLpNorm g (ENNReal.ofReal a) μ := by
  have hap : 0 < a := by linarith
  have hpa : (1 : ℝ≥0∞) ≤ ENNReal.ofReal a := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha.le
  by_cases hzero : eLpNorm g (ENNReal.ofReal a) μ = 0
  · have hz := (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hap).ne').mp hzero
    have he : T g = (fun _ ↦ 0) := by
      funext x
      rw [T.congr_ae hz x]
      exact T.map_zero x
    simp [he, hzero]
  let N := eLpNorm g (ENNReal.ofReal a) μ
  have hNt : N ≠ ⊤ := hga.eLpNorm_ne_top
  have hNz : N ≠ 0 := hzero
  have hNp : 0 < N.toReal := ENNReal.toReal_pos hNz hNt
  let c : ℂ := (N.toReal : ℂ)⁻¹
  have hNnorm : ‖(N.toReal : ℂ)‖ₑ = N := by
    rw [← ofReal_norm]
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNp] using
      ENNReal.ofReal_toReal hNt
  have hcnorm : ‖c‖ₑ = N⁻¹ := by
    change ‖(N.toReal : ℂ)⁻¹‖ₑ = N⁻¹
    rw [enorm_inv, hNnorm]
    exact_mod_cast hNp.ne'
  let g' : X → ℂ := c • g
  have hgm' : Measurable g' := hgm.const_smul c
  have hgi' : Integrable g' μ := (MemLp.integrable hpa hga).const_mul c
  have hgnorm : eLpNorm g' (ENNReal.ofReal a) μ = 1 := by
    rw [show g' = c • g from rfl, eLpNorm_const_smul, hcnorm]
    exact ENNReal.inv_mul_cancel hNz hNt
  have hgmoment : (∫⁻ ω, ‖g' ω‖ₑ ^ a ∂μ) ≤ 1 := by
    rw [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hap hgm'.aestronglyMeasurable, hgnorm,
      ENNReal.one_rpow]
  have H := FiniteExtension.mixed_normalized ha has hb hab hdiag hgm' hgi' hgmoment
  have hrestore : g = (N.toReal : ℂ) • g' := by
    funext ω
    change g ω = (N.toReal : ℂ) * ((N.toReal : ℂ)⁻¹ * g ω)
    rw [← mul_assoc, mul_inv_cancel₀ (show (N.toReal : ℂ) ≠ 0 by exact_mod_cast hNp.ne'), one_mul]
  have hErestore : T g = (N.toReal : ℂ) • T g' := by
    funext x
    calc
      _ = T ((N.toReal : ℂ) • g') x := congrArg (fun f ↦ T f x) hrestore
      _ = _ := T.map_const_mul (N.toReal : ℂ) g' x
  rw [hErestore, eLpNorm_const_smul, hNnorm]
  calc
    _ ≤ N * FiniteExtension.mixedExtensionConstant μ a s b C := by gcongr
    _ = _ := mul_comm _ _

/-- A diagonal spherical extension estimate implies the strict mixed estimate
above its interpolation line, for every input in the actual `Lᵃ` space. -/
theorem mixed {a s b : ℝ}
    (ha : 1 < a) (has : a ≤ s) (hb : 0 < b)
    (hab : a * (s - 1) / (a - 1) < b) {C : ℝ≥0∞}
    (hdiag : ∀ g : X → ℂ, MemLp g (ENNReal.ofReal s) μ →
      eLpNorm (T g) (ENNReal.ofReal s) ν ≤
        C * eLpNorm g (ENNReal.ofReal s) μ)
    {g : X → ℂ} (hga : MemLp g (ENNReal.ofReal a) μ) :
    eLpNorm (T g) (ENNReal.ofReal b) ν ≤
      FiniteExtension.mixedExtensionConstant μ a s b C * eLpNorm g (ENNReal.ofReal a) μ := by
  let g' := hga.aestronglyMeasurable.mk g
  have heq : g =ᵐ[μ] g' := hga.aestronglyMeasurable.ae_eq_mk
  have hgm' : Measurable g' := hga.aestronglyMeasurable.measurable_mk
  have hga' : MemLp g' (ENNReal.ofReal a) μ := by
    rw [MemLp, ← eLpNorm_congr_ae heq]
    exact hga
  have H := FiniteExtension.mixed_of_measurable ha has hb hab hdiag hgm' hga'
  have hE : T g = T g' := funext (T.congr_ae heq)
  rwa [← hE, ← eLpNorm_congr_ae heq] at H

end OAI.Analysis.Fourier.Cone.FiniteExtension
