import OAI.Topology.Pontryagin.Convolution
import OAI.Topology.Pontryagin.Density
import OAI.Topology.Pontryagin.DualPolars

/-! # Fourier Transform -/

namespace OAI.Topology.Pontryagin.FourierTransform

noncomputable section

open _root_.Circle
open _root_.PontryaginDual

/-!
# The Fourier transform on a locally compact abelian group

For a locally compact Hausdorff abelian group `G` with regular Haar measure `μ`, this file
defines the Fourier transform of `f: G → ℂ` as the function on the Pontryagin dual

`fourierTransform μ f χ = ∫ x, f x * conj (χ x: ℂ) ∂μ`

and develops its basic theory for integrable `f`.

## Main definitions

* `fourierTransform μ f`: the Fourier transform of `f`, a function `PontryaginDual G → ℂ`.

## Main results

* Linearity and the `L¹` bound: `fourierTransform_add`, `fourierTransform_sub`,
 `fourierTransform_smul`, `norm_fourierTransform_le`, `norm_fourierTransform_sub_le`,
 together with `MeasureTheory.Integrable.mul_conj_char` (integrability of the integrand)
 and `fourierTransform_congr_ae`.
* Symmetries: `fourierTransform_mstar` (the transform intertwines the star involution with
 complex conjugation), `fourierTransform_mtranslate` (translation becomes modulation) and
 `fourierTransform_mul_char` (modulation becomes translation in the dual).
* `fourierTransform_mconv`: the transform of a convolution of two continuous compactly
 supported functions is the product of the transforms.
* `continuous_fourierTransform`: the Fourier transform of an integrable function is
 continuous on the dual group.
* `tendsto_fourierTransform_cocompact` (**Riemann–Lebesgue lemma**): the Fourier transform
 of an integrable function vanishes at infinity on the dual group. The proof combines the
 translation identity with compactness of polars of neighborhoods of `1`
 (`PontryaginDual.isCompact_polar`) and continuity of translation on `L¹`.
* `exists_nhds_forall_bump_fourierTransform_close`: Fourier transforms of normalized bumps
 supported near `1` are uniformly close to `1` on compact subsets of the dual group.
-/

open Filter Function _root_.MeasureTheory Real Set _root_.Topology
open scoped ComplexConjugate ENNReal

-- The main section below deliberately uses one coarse hypothesis block (locally compact
-- Hausdorff abelian group with regular Haar measure) rather than minimal per-lemma assumptions.

/-! ### A chord bound on the circle -/

namespace Circle

/-- Points of the circle whose argument stays away from `0` are quantitatively far from `1`:
if `π / 4 ≤ |arg z|` then `√2 / 2 ≤ ‖(z: ℂ) - 1‖`. -/
theorem sqrt_two_div_two_le_norm_coe_sub_one {z : Circle}
    (hz : π / 4 ≤ |Complex.arg (z : ℂ)|) :
    Real.sqrt 2 / 2 ≤ ‖(z : ℂ) - 1‖ := by
  obtain ⟨t, ht1, ht2, rfl⟩ : ∃ t : ℝ, -π < t ∧ t ≤ π ∧ Circle.exp t = z :=
    ⟨Complex.arg z, Complex.neg_pi_lt_arg z, Complex.arg_le_pi z, Circle.exp_arg z⟩
  rw [Circle.arg_exp ht1 ht2] at hz
  rw [Circle.coe_exp]
  have hcos : Real.cos t ≤ Real.sqrt 2 / 2 := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_four]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (abs_le.mpr ⟨ht1.le, ht2⟩) hz
  have hre : (Complex.exp ((t : ℂ) * Complex.I) - 1).re = Real.cos t - 1 := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp ((t : ℂ) * Complex.I) - 1).im = Real.sin t := by
    simp [Complex.exp_ofReal_mul_I_im]
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (Real.sqrt 2 / 2) ^ 2 ≤ ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sqrt_nonneg 2,
      sq_nonneg (Real.sqrt 2 - 3 / 2)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

end Circle

namespace PontryaginDual

/-! ### Comparing two characters through their quotient -/

section DualHelpers

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The pointwise distance of two characters is the pointwise distance of their quotient
from `1`. -/
theorem norm_coe_sub_coe (χ χ₀ : PontryaginDual G) (x : G) :
    ‖(χ x : ℂ) - (χ₀ x : ℂ)‖ = ‖((χ / χ₀) x : ℂ) - 1‖ := by
  have hsplit : (χ x : ℂ) - (χ₀ x : ℂ) = (((χ / χ₀) x : ℂ) - 1) * (χ₀ x : ℂ) := by
    have hdiv : (χ / χ₀) x = χ x / χ₀ x := rfl
    rw [hdiv, Circle.coe_div, sub_mul, one_mul,
      div_mul_cancel₀ _ (Circle.coe_ne_zero (χ₀ x))]
  rw [hsplit, norm_mul, Circle.norm_coe, mul_one]

end DualHelpers

/-! ### Definition and measure-independent lemmas -/

section Def

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]

/-- The Fourier transform of `f: G → ℂ` with respect to the measure `μ`, as a function on
the Pontryagin dual: `fourierTransform μ f χ = ∫ x, f x * conj (χ x) ∂μ`. -/
def fourierTransform (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) : ℂ :=
  ∫ x, f x * conj (χ x : ℂ) ∂μ

theorem fourierTransform_apply (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) :
    fourierTransform μ f χ = ∫ x, f x * conj (χ x : ℂ) ∂μ := rfl

/-- The Fourier transform only depends on the almost-everywhere class. -/
theorem fourierTransform_congr_ae {μ : Measure G} {f g : G → ℂ} (h : f =ᵐ[μ] g) :
    fourierTransform μ f = fourierTransform μ g := by
  funext χ
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The Fourier transform is homogeneous. -/
theorem fourierTransform_smul (μ : Measure G) (c : ℂ) (f : G → ℂ) :
    fourierTransform μ (c • f) = c • fourierTransform μ f := by
  funext χ
  calc fourierTransform μ (c • f) χ
      = ∫ x, c * (f x * conj (χ x : ℂ)) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp [mul_assoc]
    _ = c * fourierTransform μ f χ := integral_const_mul _ _
    _ = (c • fourierTransform μ f) χ := rfl

/-- The trivial `L¹` bound for the Fourier transform. -/
theorem norm_fourierTransform_le (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) :
    ‖fourierTransform μ f χ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  rw [fourierTransform_apply]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one]

end Def

/-! ### The Fourier transform over a Haar measure -/

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

variable {f g : G → ℂ}

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The integrand of the Fourier transform of an integrable function is integrable. -/
theorem _root_.OAI.Topology.Pontryagin.FourierTransform.MeasureTheory.Integrable.mul_conj_char (hf : Integrable f μ)
    (χ : PontryaginDual G) : Integrable (fun x => f x * conj (χ x : ℂ)) μ :=
  hf.mul_bdd (c := 1)
    ((Complex.continuous_conj.comp
      (continuous_induced_dom.comp (map_continuous χ))).aestronglyMeasurable)
    (Eventually.of_forall fun x => by rw [RCLike.norm_conj, Circle.norm_coe])

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The Fourier transform is additive on integrable functions. -/
theorem fourierTransform_add (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierTransform μ (f + g) = fourierTransform μ f + fourierTransform μ g := by
  funext χ
  calc fourierTransform μ (f + g) χ
      = ∫ x, (f x * conj (χ x : ℂ) + g x * conj (χ x : ℂ)) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply, add_mul]
    _ = fourierTransform μ f χ + fourierTransform μ g χ :=
        integral_add (MeasureTheory.Integrable.mul_conj_char (μ := μ) hf χ) (MeasureTheory.Integrable.mul_conj_char (μ := μ) hg χ)
    _ = (fourierTransform μ f + fourierTransform μ g) χ := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The Fourier transform is subtractive on integrable functions. -/
theorem fourierTransform_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    fourierTransform μ (f - g) = fourierTransform μ f - fourierTransform μ g := by
  funext χ
  calc fourierTransform μ (f - g) χ
      = ∫ x, (f x * conj (χ x : ℂ) - g x * conj (χ x : ℂ)) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Pi.sub_apply, sub_mul]
    _ = fourierTransform μ f χ - fourierTransform μ g χ :=
        integral_sub (MeasureTheory.Integrable.mul_conj_char (μ := μ) hf χ) (MeasureTheory.Integrable.mul_conj_char (μ := μ) hg χ)
    _ = (fourierTransform μ f - fourierTransform μ g) χ := rfl

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [μ.IsHaarMeasure] [μ.Regular] in
/-- `L¹` bound for the difference of two Fourier transforms. -/
theorem norm_fourierTransform_sub_le (hf : Integrable f μ) (hg : Integrable g μ)
    (χ : PontryaginDual G) :
    ‖fourierTransform μ f χ - fourierTransform μ g χ‖ ≤ ∫ x, ‖f x - g x‖ ∂μ := by
  have hsub : ∫ x, (f x - g x) * conj (χ x : ℂ) ∂μ
      = fourierTransform μ f χ - fourierTransform μ g χ :=
    calc ∫ x, (f x - g x) * conj (χ x : ℂ) ∂μ
        = ∫ x, (f x * conj (χ x : ℂ) - g x * conj (χ x : ℂ)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          ring
      _ = fourierTransform μ f χ - fourierTransform μ g χ :=
          integral_sub (MeasureTheory.Integrable.mul_conj_char (μ := μ) hf χ) (MeasureTheory.Integrable.mul_conj_char (μ := μ) hg χ)
  rw [← hsub]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one]

omit [T2Space G] in
/-- The Fourier transform intertwines the star involution `mstar` with complex
conjugation. -/
theorem fourierTransform_mstar (f : G → ℂ) (χ : PontryaginDual G) :
    fourierTransform μ (Convolution.MeasureTheory.mstar f) χ = conj (fourierTransform μ f χ) := by
  calc fourierTransform μ (Convolution.MeasureTheory.mstar f) χ
      = ∫ x, conj (f x⁻¹ * conj (χ x⁻¹ : ℂ)) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Convolution.MeasureTheory.mstar_apply, _root_.map_mul, map_inv, Circle.coe_inv_eq_conj, RCLike.conj_conj]
    _ = ∫ x, conj (f x * conj (χ x : ℂ)) ∂μ :=
        integral_inv_eq_self (fun x => conj (f x * conj (χ x : ℂ))) μ
    _ = conj (fourierTransform μ f χ) := integral_conj

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- Translation becomes modulation under the Fourier transform:
`𝓕 (_root_.OAI.Topology.Pontryagin.Translation.MeasureTheory.mtranslate a f) χ = conj (χ a) * 𝓕 f χ`. -/
theorem fourierTransform_mtranslate (f : G → ℂ) (a : G) (χ : PontryaginDual G) :
    fourierTransform μ (Translation.MeasureTheory.mtranslate a f) χ = conj (χ a : ℂ) * fourierTransform μ f χ := by
  calc fourierTransform μ (Translation.MeasureTheory.mtranslate a f) χ
      = ∫ x, f (a⁻¹ * (a * x)) * conj (χ (a * x) : ℂ) ∂μ :=
        (integral_mul_left_eq_self (fun x => f (a⁻¹ * x) * conj (χ x : ℂ)) a).symm
    _ = ∫ x, conj (χ a : ℂ) * (f x * conj (χ x : ℂ)) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [inv_mul_cancel_left, _root_.map_mul, Circle.coe_mul]
        ring
    _ = conj (χ a : ℂ) * fourierTransform μ f χ := integral_const_mul _ _

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- Modulation becomes translation in the dual group under the Fourier transform:
`𝓕 (f · η) χ = 𝓕 f (χ / η)`. -/
theorem fourierTransform_mul_char (f : G → ℂ) (η χ : PontryaginDual G) :
    fourierTransform μ (fun x => f x * (η x : ℂ)) χ = fourierTransform μ f (χ / η) := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change f x * (η x : ℂ) * conj (χ x : ℂ) = f x * conj ((χ / η) x : ℂ)
  have hkey : conj (((χ / η) x : Circle) : ℂ) = conj (χ x : ℂ) * (η x : ℂ) := by
    have hdiv : (χ / η) x = χ x / η x := rfl
    rw [hdiv, ← Circle.coe_inv_eq_conj, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
    congr 1
    rw [inv_div, div_eq_mul_inv, mul_comm]
  rw [hkey]
  ring

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- The Fourier transform maps convolution of continuous compactly supported functions to
pointwise multiplication. -/
theorem fourierTransform_mconv (hf : Continuous f) (hf' : HasCompactSupport f)
    (hg : Continuous g) (hg' : HasCompactSupport g) (χ : PontryaginDual G) :
    fourierTransform μ (Convolution.MeasureTheory.mconv μ f g) χ = fourierTransform μ f χ * fourierTransform μ g χ := by
  have hχcont : Continuous fun x : G => conj (χ x : ℂ) :=
    Complex.continuous_conj.comp (continuous_induced_dom.comp (map_continuous χ))
  have hkc : Continuous (uncurry fun x y : G => f y * g (y⁻¹ * x) * conj (χ x : ℂ)) :=
    (Convolution.MeasureTheory.mconv_kernel_continuous hf hg).mul (hχcont.comp continuous_fst)
  have hks : HasCompactSupport (uncurry fun x y : G => f y * g (y⁻¹ * x) * conj (χ x : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((hf'.isCompact.mul hg'.isCompact).prod hf'.isCompact) fun p hp => ?_
    have hp' : f p.2 * g (p.2⁻¹ * p.1) ≠ 0 := left_ne_zero_of_mul hp
    exact Convolution.MeasureTheory.mconv_kernel_support_subset hp'
  calc fourierTransform μ (Convolution.MeasureTheory.mconv μ f g) χ
      = ∫ x, ∫ y, f y * g (y⁻¹ * x) * conj (χ x : ℂ) ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ y, ∫ x, f y * g (y⁻¹ * x) * conj (χ x : ℂ) ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hkc hks
    _ = ∫ y, f y * conj (χ y : ℂ) * fourierTransform μ g χ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        calc ∫ x, f y * g (y⁻¹ * x) * conj (χ x : ℂ) ∂μ
            = ∫ x, f y * (g (y⁻¹ * x) * conj (χ x : ℂ)) ∂μ := by
              refine integral_congr_ae (Eventually.of_forall fun x => ?_)
              ring
          _ = f y * ∫ x, g (y⁻¹ * x) * conj (χ x : ℂ) ∂μ := integral_const_mul _ _
          _ = f y * fourierTransform μ (Translation.MeasureTheory.mtranslate y g) χ := rfl
          _ = f y * (conj (χ y : ℂ) * fourierTransform μ g χ) := by
              rw [fourierTransform_mtranslate μ g y χ]
          _ = f y * conj (χ y : ℂ) * fourierTransform μ g χ := by ring
    _ = (∫ y, f y * conj (χ y : ℂ) ∂μ) * fourierTransform μ g χ := integral_mul_const _ _
    _ = fourierTransform μ f χ * fourierTransform μ g χ := rfl

/-! ### Continuity of the Fourier transform -/

omit [IsTopologicalGroup G] [μ.IsHaarMeasure] in
/-- The Fourier transform of an integrable function is a continuous function on the
Pontryagin dual. -/
theorem continuous_fourierTransform (hf : Integrable f μ) :
    Continuous (fourierTransform μ f) := by
  rw [continuous_iff_continuousAt]
  intro χ₀
  have key : Tendsto (fourierTransform μ f) (nhds χ₀)
      (nhds (fourierTransform μ f χ₀)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨v, hvc, hvs, hvi, hvclose⟩ :=
      Density.MeasureTheory.exists_hasCompactSupport_integral_norm_sub_le hf
        (show (0 : ℝ) < ε / 4 by linarith)
    set I : ℝ := ∫ x, ‖v x‖ ∂μ with hIdef
    have hI0 : (0 : ℝ) ≤ I := integral_nonneg fun x => norm_nonneg _
    have hden : (0 : ℝ) < 4 * (I + 1) := by linarith
    set r : ℝ := min π (ε / (4 * (I + 1))) with hrdef
    have hrpos : 0 < r := lt_min Real.pi_pos (div_pos hε hden)
    have hrπ : r ≤ π := min_le_left _ _
    have hdiv : Tendsto (fun χ : PontryaginDual G => χ / χ₀) (nhds χ₀) (nhds 1) := by
      have hc : Continuous fun χ : PontryaginDual G => χ / χ₀ :=
        continuous_id.div' continuous_const
      have h2 := hc.tendsto χ₀
      rwa [div_self'] at h2
    filter_upwards [hdiv.eventually
      (DualPolars.PontryaginDual.eventually_uniform_arc hvs.isCompact hrpos hrπ)] with χ hχ
    rw [dist_eq_norm]
    have h1 : ‖fourierTransform μ f χ - fourierTransform μ v χ‖ ≤ ε / 4 :=
      (norm_fourierTransform_sub_le μ hf hvi χ).trans hvclose
    have hvclose' : ∫ x, ‖v x - f x‖ ∂μ ≤ ε / 4 := by
      have heq : ∫ x, ‖v x - f x‖ ∂μ = ∫ x, ‖f x - v x‖ ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev _ _)
      rw [heq]
      exact hvclose
    have h3 : ‖fourierTransform μ v χ₀ - fourierTransform μ f χ₀‖ ≤ ε / 4 :=
      (norm_fourierTransform_sub_le μ hvi hf χ₀).trans hvclose'
    have h2 : ‖fourierTransform μ v χ - fourierTransform μ v χ₀‖ ≤ r * I := by
      have hsub : ∫ x, v x * (conj (χ x : ℂ) - conj (χ₀ x : ℂ)) ∂μ
          = fourierTransform μ v χ - fourierTransform μ v χ₀ :=
        calc ∫ x, v x * (conj (χ x : ℂ) - conj (χ₀ x : ℂ)) ∂μ
            = ∫ x, (v x * conj (χ x : ℂ) - v x * conj (χ₀ x : ℂ)) ∂μ := by
              refine integral_congr_ae (Eventually.of_forall fun x => ?_)
              ring
          _ = fourierTransform μ v χ - fourierTransform μ v χ₀ :=
              integral_sub (MeasureTheory.Integrable.mul_conj_char (μ := μ) hvi χ) (MeasureTheory.Integrable.mul_conj_char (μ := μ) hvi χ₀)
      have hIeq : r * I = ∫ x, r * ‖v x‖ ∂μ := (integral_const_mul _ _).symm
      rw [← hsub, hIeq]
      refine norm_integral_le_of_norm_le (hvi.norm.const_mul r)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      by_cases hx : x ∈ tsupport v
      · have hb : ‖conj (χ x : ℂ) - conj (χ₀ x : ℂ)‖ ≤ r := by
          rw [← map_sub, RCLike.norm_conj, norm_coe_sub_coe]
          exact (hχ x hx).le
        calc ‖v x‖ * ‖conj (χ x : ℂ) - conj (χ₀ x : ℂ)‖
            ≤ ‖v x‖ * r := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = r * ‖v x‖ := mul_comm _ _
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
    have hrI : r * I < ε / 4 := by
      have hr2 : r ≤ ε / (4 * (I + 1)) := min_le_right _ _
      have h4 : r * I ≤ ε / (4 * (I + 1)) * I := mul_le_mul_of_nonneg_right hr2 hI0
      have h5 : ε / (4 * (I + 1)) * I < ε / 4 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
        nlinarith
      linarith
    have hsplit : fourierTransform μ f χ - fourierTransform μ f χ₀
        = (fourierTransform μ f χ - fourierTransform μ v χ) +
          ((fourierTransform μ v χ - fourierTransform μ v χ₀) +
            (fourierTransform μ v χ₀ - fourierTransform μ f χ₀)) := by ring
    calc ‖fourierTransform μ f χ - fourierTransform μ f χ₀‖
        = ‖(fourierTransform μ f χ - fourierTransform μ v χ) +
            ((fourierTransform μ v χ - fourierTransform μ v χ₀) +
              (fourierTransform μ v χ₀ - fourierTransform μ f χ₀))‖ := by rw [hsplit]
      _ ≤ ‖fourierTransform μ f χ - fourierTransform μ v χ‖ +
            (‖fourierTransform μ v χ - fourierTransform μ v χ₀‖ +
              ‖fourierTransform μ v χ₀ - fourierTransform μ f χ₀‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ < ε := by linarith
  exact key

/-! ### The Riemann–Lebesgue lemma -/

omit [T2Space G] in
/-- **Riemann–Lebesgue lemma**: the Fourier transform of an integrable function vanishes at
infinity on the Pontryagin dual. -/
theorem tendsto_fourierTransform_cocompact (hf : Integrable f μ) :
    Tendsto (fourierTransform μ f) (cocompact (PontryaginDual G)) (nhds 0) := by
  refine (Filter.hasBasis_cocompact.tendsto_iff Metric.nhds_basis_closedBall).mpr
    fun ε hε => ?_
  have hδ₀pos : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  set F : Lp ℂ 1 μ := hf.toL1 f with hFdef
  have hcont : Continuous fun y : G => Translation.MeasureTheory.translateLp μ 1 y F :=
    Translation.MeasureTheory.continuous_translateLp μ 1 ENNReal.one_ne_top F
  set U : Set G := {y : G | ‖Translation.MeasureTheory.translateLp μ 1 y F - F‖ < ε * (Real.sqrt 2 / 2)} with hUdef
  have hUnhds : U ∈ nhds (1 : G) := by
    have h0 : Set.Iio (ε * (Real.sqrt 2 / 2))
        ∈ nhds ((fun y : G => ‖Translation.MeasureTheory.translateLp μ 1 y F - F‖) 1) := by
      have h1 : ‖Translation.MeasureTheory.translateLp μ 1 (1 : G) F - F‖ = 0 := by
        rw [Translation.MeasureTheory.translateLp_one, sub_self, norm_zero]
      simpa [h1] using Iio_mem_nhds (mul_pos hε hδ₀pos)
    exact ((hcont.sub continuous_const).norm.continuousAt).preimage_mem_nhds h0
  refine ⟨DualPolars.PontryaginDual.polar U, DualPolars.PontryaginDual.isCompact_polar hUnhds, fun χ hχ => ?_⟩
  rw [mem_closedBall_zero_iff]
  obtain ⟨y, hyU, hyarc⟩ : ∃ y ∈ U, χ y ∉ closure (Circle.centeredArc (π / 4)) := by
    by_contra hcon
    push Not at hcon
    exact hχ fun y hy => hcon y hy
  have harg : π / 4 ≤ |Complex.arg (χ y : ℂ)| := by
    by_contra hcon
    push Not at hcon
    exact hyarc ((DualPolars.Circle.mem_closure_centeredArc (by positivity)
      (by linarith [Real.pi_pos])).mpr hcon.le)
  have hchord : Real.sqrt 2 / 2 ≤ ‖(χ y : ℂ) - 1‖ :=
    FourierTransform.Circle.sqrt_two_div_two_le_norm_coe_sub_one harg
  have hf1 : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
  have hft : Integrable (Translation.MeasureTheory.mtranslate y f) μ :=
    memLp_one_iff_integrable.mp (Translation.MeasureTheory.MemLp.mtranslate μ hf1 y)
  have hbridge : ∫ x, ‖Translation.MeasureTheory.mtranslate y f x - f x‖ ∂μ = ‖Translation.MeasureTheory.translateLp μ 1 y F - F‖ := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    have hc : ⇑F =ᵐ[μ] f := hf.coeFn_toL1
    have hd : Translation.MeasureTheory.mtranslate y ⇑F =ᵐ[μ] Translation.MeasureTheory.mtranslate y f :=
      (measurePreserving_mul_left μ y⁻¹).quasiMeasurePreserving.ae_eq_comp hc
    filter_upwards [Lp.coeFn_sub (Translation.MeasureTheory.translateLp μ 1 y F) F, Translation.MeasureTheory.coeFn_translateLp μ 1 y F,
      hd, hc] with x hx1 hx2 hx3 hx4
    rw [hx1, Pi.sub_apply, hx2, hx3, hx4]
  have hyU' : ‖Translation.MeasureTheory.translateLp μ 1 y F - F‖ < ε * (Real.sqrt 2 / 2) := hyU
  have hlt : ‖fourierTransform μ (Translation.MeasureTheory.mtranslate y f) χ - fourierTransform μ f χ‖
      < ε * (Real.sqrt 2 / 2) :=
    calc ‖fourierTransform μ (Translation.MeasureTheory.mtranslate y f) χ - fourierTransform μ f χ‖
        ≤ ∫ x, ‖Translation.MeasureTheory.mtranslate y f x - f x‖ ∂μ := norm_fourierTransform_sub_le μ hft hf χ
      _ = ‖Translation.MeasureTheory.translateLp μ 1 y F - F‖ := hbridge
      _ < ε * (Real.sqrt 2 / 2) := hyU'
  have hconj : ‖conj ((χ y : Circle) : ℂ) - 1‖ = ‖(χ y : ℂ) - 1‖ := by
    rw [show conj ((χ y : Circle) : ℂ) - 1 = conj ((χ y : ℂ) - 1) by rw [map_sub, _root_.map_one],
      RCLike.norm_conj]
  have hmul : Real.sqrt 2 / 2 * ‖fourierTransform μ f χ‖ < ε * (Real.sqrt 2 / 2) :=
    calc Real.sqrt 2 / 2 * ‖fourierTransform μ f χ‖
        ≤ ‖(χ y : ℂ) - 1‖ * ‖fourierTransform μ f χ‖ :=
          mul_le_mul_of_nonneg_right hchord (norm_nonneg _)
      _ = ‖(conj ((χ y : Circle) : ℂ) - 1) * fourierTransform μ f χ‖ := by
          rw [norm_mul, hconj]
      _ = ‖fourierTransform μ (Translation.MeasureTheory.mtranslate y f) χ - fourierTransform μ f χ‖ := by
          rw [fourierTransform_mtranslate μ f y χ]
          congr 1
          ring
      _ < ε * (Real.sqrt 2 / 2) := hlt
  have hfinal : ‖fourierTransform μ f χ‖ < ε := by
    have h2 : Real.sqrt 2 / 2 * ‖fourierTransform μ f χ‖ < Real.sqrt 2 / 2 * ε := by
      linarith
    exact lt_of_mul_lt_mul_left h2 hδ₀pos.le
  exact hfinal.le

/-! ### Transforms of normalized bumps -/

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- On a compact set of characters, all characters are uniformly close to `1` on a suitable
neighborhood of `1` in `G`. -/
private theorem exists_nhds_forall_norm_sub_one_le {K : Set (PontryaginDual G)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : G), ∀ χ ∈ K, ∀ x ∈ U, ‖(χ x : ℂ) - 1‖ ≤ ε := by
  obtain ⟨C, hCcomp, hCnhds⟩ := exists_compact_mem_nhds (1 : G)
  have hrpos : 0 < min (ε / 2) π := lt_min (by linarith) Real.pi_pos
  set N : Set (PontryaginDual G) :=
    {ψ | ∀ x ∈ C, ‖(ψ x : ℂ) - 1‖ < min (ε / 2) π} with hNdef
  have hN : N ∈ nhds (1 : PontryaginDual G) :=
    DualPolars.PontryaginDual.eventually_uniform_arc hCcomp hrpos (min_le_right _ _)
  have hUχ : ∀ χ₀ : PontryaginDual G,
      (fun χ : PontryaginDual G => χ / χ₀) ⁻¹' N ∈ nhds χ₀ := by
    intro χ₀
    have hc : Continuous fun χ : PontryaginDual G => χ / χ₀ :=
      continuous_id.div' continuous_const
    have h1 : N ∈ nhds ((fun χ : PontryaginDual G => χ / χ₀) χ₀) := by
      simpa [div_self'] using hN
    exact hc.continuousAt.preimage_mem_nhds h1
  obtain ⟨t, -, hcover⟩ :=
    hK.elim_nhds_subcover (fun χ₀ => (fun χ : PontryaginDual G => χ / χ₀) ⁻¹' N)
      fun χ₀ _ => hUχ χ₀
  have hVmem : ∀ χ₀ : PontryaginDual G,
      {x : G | ‖(χ₀ x : ℂ) - 1‖ < ε / 2} ∈ nhds (1 : G) := by
    intro χ₀
    have hc : Continuous fun x : G => ‖(χ₀ x : ℂ) - 1‖ :=
      ((continuous_induced_dom.comp (map_continuous χ₀)).sub continuous_const).norm
    have h1 : Set.Iio (ε / 2) ∈ nhds ((fun x : G => ‖(χ₀ x : ℂ) - 1‖) 1) := by
      have h2 : ((χ₀ (1 : G) : Circle) : ℂ) = 1 := by rw [_root_.map_one, Circle.coe_one]
      simpa [h2] using Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 2)
    exact hc.continuousAt.preimage_mem_nhds h1
  refine ⟨C ∩ ⋂ χ₀ ∈ t, {x : G | ‖(χ₀ x : ℂ) - 1‖ < ε / 2},
    Filter.inter_mem hCnhds ((Filter.biInter_finset_mem t).mpr fun χ₀ _ => hVmem χ₀),
    fun χ hχK x hx => ?_⟩
  obtain ⟨hxC, hxV⟩ := hx
  obtain ⟨χ₀, hχ₀t, hχdiv⟩ : ∃ χ₀ ∈ t, χ / χ₀ ∈ N := by
    have h := hcover hχK
    simpa only [Set.mem_iUnion, Set.mem_preimage, exists_prop] using h
  have h1 : ‖(χ x : ℂ) - (χ₀ x : ℂ)‖ ≤ ε / 2 := by
    rw [norm_coe_sub_coe]
    exact ((hχdiv x hxC).trans_le (min_le_left _ _)).le
  have h2 : ‖(χ₀ x : ℂ) - 1‖ ≤ ε / 2 := (Set.mem_iInter₂.mp hxV χ₀ hχ₀t).le
  calc ‖(χ x : ℂ) - 1‖
      = ‖((χ x : ℂ) - (χ₀ x : ℂ)) + ((χ₀ x : ℂ) - 1)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖(χ x : ℂ) - (χ₀ x : ℂ)‖ + ‖(χ₀ x : ℂ) - 1‖ := norm_add_le _ _
    _ ≤ ε := by linarith

omit [IsTopologicalGroup G] [T2Space G] [μ.Regular] in
/-- Uniform smallness of bump transforms: given a compact set `K` of characters and `ε > 0`,
there is a neighborhood `U` of `1` in `G` such that the Fourier transform of every
normalized bump supported in `U` is within `ε` of `1`, uniformly on `K`. -/
theorem exists_nhds_forall_bump_fourierTransform_close {K : Set (PontryaginDual G)}
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : G), ∀ h : G → ℝ, Continuous h → HasCompactSupport h →
      (∀ x, 0 ≤ h x) → tsupport h ⊆ U → (∫ x, h x ∂μ) = 1 →
      ∀ χ ∈ K, ‖fourierTransform μ (fun x => (h x : ℂ)) χ - 1‖ ≤ ε := by
  obtain ⟨U, hU, hUsmall⟩ := exists_nhds_forall_norm_sub_one_le hK hε
  refine ⟨U, hU, fun h hhc hhs hhpos hhsupp hhone χ hχK => ?_⟩
  have hhC : Continuous fun x : G => (h x : ℂ) := Complex.continuous_ofReal.comp hhc
  have hhCs : HasCompactSupport fun x : G => (h x : ℂ) :=
    hhs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hhCint : Integrable (fun x : G => (h x : ℂ)) μ :=
    hhC.integrable_of_hasCompactSupport hhCs
  have hhint : Integrable h μ := hhc.integrable_of_hasCompactSupport hhs
  have honeC : ∫ x, (h x : ℂ) ∂μ = 1 := by
    have hcast : ∫ x, (h x : ℂ) ∂μ = ((∫ x, h x ∂μ : ℝ) : ℂ) := integral_ofReal
    rw [hcast, hhone, Complex.ofReal_one]
  have hsub : ∫ x, (h x : ℂ) * (conj (χ x : ℂ) - 1) ∂μ
      = fourierTransform μ (fun x => (h x : ℂ)) χ - 1 := by
    calc ∫ x, (h x : ℂ) * (conj (χ x : ℂ) - 1) ∂μ
        = ∫ x, ((h x : ℂ) * conj (χ x : ℂ) - (h x : ℂ)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          ring
      _ = (∫ x, (h x : ℂ) * conj (χ x : ℂ) ∂μ) - ∫ x, (h x : ℂ) ∂μ :=
          integral_sub (MeasureTheory.Integrable.mul_conj_char (μ := μ) hhCint χ) hhCint
      _ = fourierTransform μ (fun x => (h x : ℂ)) χ - 1 := by
          rw [honeC]
          rfl
  rw [← hsub]
  have hpt : ∀ x, ‖(h x : ℂ) * (conj (χ x : ℂ) - 1)‖ ≤ ε * h x := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hhpos x)]
    by_cases hx : x ∈ tsupport h
    · have hb : ‖conj (χ x : ℂ) - 1‖ ≤ ε := by
        rw [show conj ((χ x : Circle) : ℂ) - 1 = conj ((χ x : ℂ) - 1) by
          rw [map_sub, _root_.map_one], RCLike.norm_conj]
        exact hUsmall χ hχK x (hhsupp hx)
      calc h x * ‖conj (χ x : ℂ) - 1‖
          ≤ h x * ε := mul_le_mul_of_nonneg_left hb (hhpos x)
        _ = ε * h x := mul_comm _ _
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  calc ‖∫ x, (h x : ℂ) * (conj (χ x : ℂ) - 1) ∂μ‖
      ≤ ∫ x, ε * h x ∂μ :=
        norm_integral_le_of_norm_le (hhint.const_mul ε) (Eventually.of_forall hpt)
    _ = ε := by rw [integral_const_mul, hhone, mul_one]

end PontryaginDual

end

end OAI.Topology.Pontryagin.FourierTransform
