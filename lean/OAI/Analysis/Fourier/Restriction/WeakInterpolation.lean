import OAI.Analysis.Fourier.Restriction.InterpolationHead

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem measurable_tailMoment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (fun t : ℝ ↦ ∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ a ∂μ) := by
  let F : ℝ × X → ℝ≥0∞ := {z | z.1 < f z.2}.indicator
    (fun z ↦ ENNReal.ofReal (f z.2) ^ a)
  have hF : Measurable F := ((hf.comp measurable_snd).ennreal_ofReal.pow_const a).indicator
    (measurableSet_lt measurable_fst (hf.comp measurable_snd))
  have h := hF.lintegral_prod_right' (ν := μ)
  convert h using 1
  funext t
  change _ = ∫⁻ x, {x | t < f x}.indicator (fun x ↦ ENNReal.ofReal (f x) ^ a) x ∂μ
  rw [lintegral_indicator (measurableSet_lt measurable_const hf)]

theorem measurable_headMoment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (fun t : ℝ ↦ ∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ a ∂μ) := by
  let F : ℝ × X → ℝ≥0∞ := {z | f z.2 ≤ z.1}.indicator
    (fun z ↦ ENNReal.ofReal (f z.2) ^ a)
  have hF : Measurable F := ((hf.comp measurable_snd).ennreal_ofReal.pow_const a).indicator
    (measurableSet_le (hf.comp measurable_snd) measurable_fst)
  have h := hF.lintegral_prod_right' (ν := μ)
  convert h using 1
  funext t
  change _ = ∫⁻ x, {x | f x ≤ t}.indicator (fun x ↦ ENNReal.ofReal (f x) ^ a) x ∂μ
  rw [lintegral_indicator (measurableSet_le hf measurable_const)]

/-- The layer-cake part of Marcinkiewicz interpolation between exponents
one and two. The domain and target measures may differ; no a priori
integrability of the target is assumed. -/
theorem power_moment_le_of_two_truncations
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    {f : X → ℝ} {u : Y → ℝ} (hf : Measurable f) (hu : Measurable u)
    (hfn : ∀ x, 0 ≤ f x) (hun : ∀ y, 0 ≤ u y)
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) {A B : ℝ≥0∞}
    (hweak : ∀ t > 0, ν {y | t < u y} ≤
      A / ENNReal.ofReal t * (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) +
      B / ENNReal.ofReal t ^ (2 : ℝ) *
        (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ (2 : ℝ) ∂μ)) :
    (∫⁻ y, ENNReal.ofReal (u y) ^ p ∂ν) ≤
      (A * ENNReal.ofReal (p / (p - 1)) + B * ENNReal.ofReal (p / (2 - p))) *
        ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  have htail : Measurable (fun t : ℝ ↦
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) * ENNReal.ofReal t ^ (p - 2)) := by
    convert (measurable_tailMoment μ hf 1).mul
      (measurable_id.ennreal_ofReal.pow_const (p - 2)) using 1
    funext t
    simp only [Pi.mul_apply, ENNReal.rpow_one, id_eq]
  have hhead : Measurable (fun t : ℝ ↦
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ (2 : ℝ) ∂μ) * ENNReal.ofReal t ^ (p - 3)) := by
    convert (measurable_headMoment μ hf 2).mul
      (measurable_id.ennreal_ofReal.pow_const (p - 3)) using 1
    funext t
    rfl
  have hAtail : Measurable (fun t : ℝ ↦ (A * ENNReal.ofReal p) *
      ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) * ENNReal.ofReal t ^ (p - 2))) := by
    convert (measurable_const (a := A * ENNReal.ofReal p)).mul htail using 1
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | t < u y} * ENNReal.ofReal p *
        ENNReal.ofReal t ^ (p - 1) := OAI.Analysis.Fourier.SquareFunction.lintegral_power_layercake ν hu hun hp0
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
        (A * ENNReal.ofReal p) *
          ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) * ENNReal.ofReal t ^ (p - 2)) +
        (B * ENNReal.ofReal p) *
          ((∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ (2 : ℝ) ∂μ) * ENNReal.ofReal t ^ (p - 3)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 := ENNReal.ofReal_ne_zero_iff.mpr ht
      have he1 : ENNReal.ofReal t ^ (p - 2) = ENNReal.ofReal t ^ (p - 1) / ENNReal.ofReal t := by
        simpa only [show p - 1 - 1 = p - 2 by ring, ENNReal.rpow_one] using
          ENNReal.rpow_sub (x := ENNReal.ofReal t) (p - 1) 1 ht0 ENNReal.ofReal_ne_top
      have he2 : ENNReal.ofReal t ^ (p - 3) =
          ENNReal.ofReal t ^ (p - 1) / ENNReal.ofReal t ^ (2 : ℝ) := by
        simpa only [show p - 1 - 2 = p - 3 by ring] using
          ENNReal.rpow_sub (x := ENNReal.ofReal t) (p - 1) 2 ht0 ENNReal.ofReal_ne_top
      calc
        _ ≤ (A / ENNReal.ofReal t * (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) +
            B / ENNReal.ofReal t ^ (2 : ℝ) *
              (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ (2 : ℝ) ∂μ)) *
            ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) := by gcongr; exact hweak t ht
        _ = _ := by
          rw [he1, he2]
          simp only [div_eq_mul_inv]
          ring
    _ = (A * ENNReal.ofReal p) * (ENNReal.ofReal (1 / (p - 1)) *
          ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ) +
        (B * ENNReal.ofReal p) * (ENNReal.ofReal (1 / (2 - p)) *
          ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ) := by
      rw [lintegral_add_left hAtail,
        lintegral_const_mul _ htail, lintegral_const_mul _ hhead,
        OAI.Analysis.Fourier.SquareFunction.lintegral_weighted_tail μ hf hfn (by linarith : -1 < p - 2),
        lintegral_weighted_head_square μ hf hfn hp hp2]
      simp only [show p - 2 + 1 = p - 1 by ring, show p - 2 + 2 = p by ring]
    _ = _ := by
      have h1 : ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) = ENNReal.ofReal (p / (p - 1)) := by
        rw [← ENNReal.ofReal_mul hp0.le]
        congr 1
        ring
      have h2 : ENNReal.ofReal p * ENNReal.ofReal (1 / (2 - p)) = ENNReal.ofReal (p / (2 - p)) := by
        rw [← ENNReal.ofReal_mul hp0.le]
        congr 1
        ring
      simp only [← mul_assoc, add_mul]
      rw [mul_assoc A (ENNReal.ofReal p) (ENNReal.ofReal (1 / (p - 1))), h1,
        mul_assoc B (ENNReal.ofReal p) (ENNReal.ofReal (1 / (2 - p))), h2]

end OAI.Analysis.Fourier.Restriction
