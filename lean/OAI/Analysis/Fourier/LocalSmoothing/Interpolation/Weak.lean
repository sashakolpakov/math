import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Moments

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem power_moment_le_of_tail
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    {f : X → ℝ} {u : Y → ℝ} (hf : Measurable f) (hu : Measurable u)
    (hfn : ∀ x, 0 ≤ f x) (hun : ∀ y, 0 ≤ u y)
    {p q : ℝ} (hq : 0 < q) (hqp : q < p) {A : ℝ≥0∞}
    (hweak : ∀ t > 0, ν {y | t < u y} ≤
      A / ENNReal.ofReal t ^ q * ∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) :
    (∫⁻ y, ENNReal.ofReal (u y) ^ p ∂ν) ≤
      (A * ENNReal.ofReal (p / (p - q))) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  have hp : 0 < p := hq.trans hqp
  have ht : Measurable (fun t : ℝ =>
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1)) :=
    (OAI.Analysis.Fourier.Restriction.measurable_tailMoment μ hf q).mul
      (measurable_id.ennreal_ofReal.pow_const (p - q - 1))
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | t < u y} * ENNReal.ofReal p *
        ENNReal.ofReal t ^ (p - 1) := OAI.Analysis.Fourier.SquareFunction.lintegral_power_layercake ν hu hun hp
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (A * ENNReal.ofReal p) *
        ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) *
          ENNReal.ofReal t ^ (p - q - 1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
      have he : ENNReal.ofReal t ^ (p - q - 1) =
          ENNReal.ofReal t ^ (p - 1) / ENNReal.ofReal t ^ q := by
        simpa only [show p - 1 - q = p - q - 1 by ring] using
          ENNReal.rpow_sub (p - 1) q (ENNReal.ofReal_ne_zero_iff.mpr ht0) ENNReal.ofReal_ne_top
      calc
        _ ≤ (A / ENNReal.ofReal t ^ q * ∫⁻ x in {x | t < f x},
            ENNReal.ofReal (f x) ^ q ∂μ) * ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) := by
              gcongr; exact hweak t ht0
        _ = _ := by rw [he]; simp only [div_eq_mul_inv]; ring
    _ = _ := by
      rw [lintegral_const_mul _ ht,weighted_tail_power μ hf hfn hq hqp]
      have he : ENNReal.ofReal p * ENNReal.ofReal (1 / (p - q)) =
          ENNReal.ofReal (p / (p - q)) := by
        rw [← ENNReal.ofReal_mul hp.le]
        congr 1
        ring
      rw [← mul_assoc, mul_assoc A,he]

theorem power_moment_le_of_two_tails
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    {f : X → ℝ} {u : Y → ℝ} (hf : Measurable f) (hu : Measurable u)
    (hfn : ∀ x, 0 ≤ f x) (hun : ∀ y, 0 ≤ u y)
    {p q₀ q₁ : ℝ} (hq₀ : 0 < q₀) (h₀p : q₀ < p) (hp₁ : p < q₁)
    {A B : ℝ≥0∞}
    (hweak : ∀ t > 0, ν {y | t < u y} ≤
      A / ENNReal.ofReal t ^ q₀ * (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) +
      B / ENNReal.ofReal t ^ q₁ * (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q₁ ∂μ)) :
    (∫⁻ y, ENNReal.ofReal (u y) ^ p ∂ν) ≤
      (A * ENNReal.ofReal (p / (p - q₀)) + B * ENNReal.ofReal (p / (q₁ - p))) *
        ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  have hp : 0 < p := hq₀.trans h₀p
  have ht : Measurable (fun t : ℝ =>
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) *
        ENNReal.ofReal t ^ (p - q₀ - 1)) :=
    (OAI.Analysis.Fourier.Restriction.measurable_tailMoment μ hf q₀).mul
      (measurable_id.ennreal_ofReal.pow_const _)
  have hh : Measurable (fun t : ℝ =>
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q₁ ∂μ) *
        ENNReal.ofReal t ^ (p - q₁ - 1)) :=
    (OAI.Analysis.Fourier.Restriction.measurable_headMoment μ hf q₁).mul
      (measurable_id.ennreal_ofReal.pow_const _)
  have hAt : Measurable (fun t : ℝ => (A * ENNReal.ofReal p) *
      ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) *
        ENNReal.ofReal t ^ (p - q₀ - 1))) := measurable_const.mul ht
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | t < u y} * ENNReal.ofReal p *
        ENNReal.ofReal t ^ (p - 1) := OAI.Analysis.Fourier.SquareFunction.lintegral_power_layercake ν hu hun hp
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
        (A * ENNReal.ofReal p) * ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) *
          ENNReal.ofReal t ^ (p - q₀ - 1)) +
        (B * ENNReal.ofReal p) * ((∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q₁ ∂μ) *
          ENNReal.ofReal t ^ (p - q₁ - 1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
      have he (q : ℝ) : ENNReal.ofReal t ^ (p - q - 1) =
          ENNReal.ofReal t ^ (p - 1) / ENNReal.ofReal t ^ q := by
        simpa only [show p - 1 - q = p - q - 1 by ring] using
          ENNReal.rpow_sub (p - 1) q (ENNReal.ofReal_ne_zero_iff.mpr ht0) ENNReal.ofReal_ne_top
      calc
        _ ≤ (A / ENNReal.ofReal t ^ q₀ * (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) +
            B / ENNReal.ofReal t ^ q₁ * (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q₁ ∂μ)) *
              ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) := by
          gcongr; exact hweak t ht0
        _ = _ := by rw [he q₀,he q₁]; simp only [div_eq_mul_inv]; ring
    _ = _ := by
      rw [lintegral_add_left hAt,lintegral_const_mul _ ht,lintegral_const_mul _ hh,
        weighted_tail_power μ hf hfn hq₀ h₀p,weighted_head_power μ hf hfn hp hp₁]
      have he (q : ℝ) : ENNReal.ofReal p * ENNReal.ofReal (1 / q) =
          ENNReal.ofReal (p / q) := by
        rw [← ENNReal.ofReal_mul hp.le]
        congr 1
        ring
      simp only [← mul_assoc,add_mul]
      rw [mul_assoc A (ENNReal.ofReal p),he,mul_assoc B (ENNReal.ofReal p),he]

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
