import Mathlib

/-! Differentiating integrable weighted trigonometric averages with a bounded
frequency parameter. This covers both surface measure and ball densities. -/

open _root_.MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem hasDerivAt_trigIntegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w a b : X → ℝ} (hw : Integrable w μ) (ha : Measurable a) (hb : Measurable b)
    {K : ℝ} (hK : ∀ᵐ y ∂μ, |b y| ≤ K)
    {φ ψ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (ψ t) t) (hψ : Measurable ψ)
    (hφbound : ∀ t, |φ t| ≤ 1) (hψbound : ∀ t, |ψ t| ≤ 1) (x : ℝ) :
    HasDerivAt (fun t => ∫ y, w y * φ (a y + t * b y) ∂μ)
      (∫ y, w y * b y * ψ (a y + x * b y) ∂μ) x := by
  have hφm : Measurable φ := (show Continuous φ from
    (show Differentiable ℝ φ from fun t => (hφ t).differentiableAt).continuous).measurable
  have hm (t : ℝ) : Measurable (fun y => a y + t * b y) := ha.add (hb.const_mul t)
  have hi (t : ℝ) : Integrable (fun y => w y * φ (a y + t * b y)) μ := by
    apply hw.norm.mono' (hw.aestronglyMeasurable.mul ((hφm.comp (hm t)).aestronglyMeasurable))
    filter_upwards [] with y
    change |w y * φ (a y + t * b y)| ≤ |w y|
    rw [abs_mul]
    nlinarith [abs_nonneg (w y), hφbound (a y + t * b y)]
  have hd (t : ℝ) (y : X) : HasDerivAt (fun s => w y * φ (a y + s * b y))
      (w y * b y * ψ (a y + t * b y)) t := by
    have H := ((hφ (a y + t * b y)).comp t
      (((hasDerivAt_id t).mul_const (b y)).const_add (a y))).const_mul (w y)
    change HasDerivAt (fun s => w y * φ (a y + s * b y))
      (w y * (ψ (a y + t * b y) * (1 * b y))) t at H
    convert H using 1 ; ring
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun t y => w y * φ (a y + t * b y))
    (F' := fun t y => w y * b y * ψ (a y + t * b y))
    (s := Set.univ) (Filter.univ_mem : Set.univ ∈ 𝓝 x)
    (Eventually.of_forall fun t => (hi t).aestronglyMeasurable) (hi x)
    ((hw.aestronglyMeasurable.mul hb.aestronglyMeasurable).mul
      (hψ.comp (hm x)).aestronglyMeasurable)
    (bound := fun y => |w y| * K) ?_ (hw.abs.mul_const K)
    (Eventually.of_forall fun y t _ => hd t y)
  · exact H.2
  · filter_upwards [hK] with y hy
    intro t ht
    simp only [Real.norm_eq_abs, abs_mul]
    have hK0 : 0 ≤ K := (abs_nonneg _).trans hy
    calc
      |w y| * |b y| * |ψ (a y + t * b y)| ≤ |w y| * K * 1 := by
        gcongr
        exact hψbound _
      _ = _ := mul_one _

theorem hasDerivAt_cosineIntegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w a b : X → ℝ} (hw : Integrable w μ) (ha : Measurable a) (hb : Measurable b)
    {K : ℝ} (hK : ∀ᵐ y ∂μ, |b y| ≤ K) (x : ℝ) :
    HasDerivAt (fun t => ∫ y, w y * Real.cos (a y + t * b y) ∂μ)
      (∫ y, -(w y * b y * Real.sin (a y + x * b y)) ∂μ) x := by
  convert hasDerivAt_trigIntegral hw ha hb hK Real.hasDerivAt_cos
    Real.measurable_sin.neg Real.abs_cos_le_one
    (fun t => by simpa only [abs_neg] using Real.abs_sin_le_one t) x using 1
  congr 1
  funext y
  ring

theorem hasDerivAt_sineIntegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w a b : X → ℝ} (hw : Integrable w μ) (ha : Measurable a) (hb : Measurable b)
    {K : ℝ} (hK : ∀ᵐ y ∂μ, |b y| ≤ K) (x : ℝ) :
    HasDerivAt (fun t => ∫ y, w y * Real.sin (a y + t * b y) ∂μ)
      (∫ y, w y * b y * Real.cos (a y + x * b y) ∂μ) x :=
  hasDerivAt_trigIntegral hw ha hb hK Real.hasDerivAt_sin
    Real.measurable_cos Real.abs_sin_le_one Real.abs_cos_le_one x

end OAI.Analysis.Fourier.Radial
