import OAI.Topology.Pontryagin.Spectrum
import OAI.Topology.Pontryagin.StoneWeierstrass
import OAI.Topology.Pontryagin.FiniteMeasureFubini
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! # Fourier Dense -/

namespace OAI.Topology.Pontryagin.FourierDense

noncomputable section

open _root_.PontryaginDual

/-!
# Density of Fourier transforms in `C₀(Ĝ)` and Fourier–Stieltjes uniqueness

For a locally compact Hausdorff abelian group `G` with regular Haar measure `μ`, this file
proves that the Fourier transforms of continuous compactly supported functions are dense in
`C₀(Ĝ, ℂ)`, the continuous functions vanishing at infinity on the Pontryagin dual, and
deduces the uniqueness theorem for Fourier–Stieltjes transforms of finite positive regular
measures on the dual group.

## Main definitions

* `ccFourierC0 μ f hfc hfs`: the Fourier transform of a continuous compactly supported
 `f: G → ℂ`, bundled as an element of `C₀(Ĝ, ℂ)` (continuity plus Riemann–Lebesgue);
* `ccFourierSubalgebra μ`: the set of all such transforms, as a non-unital star subalgebra
 of `C₀(Ĝ, ℂ)` (closed under multiplication by `fourierTransform_mconv`, under star by
 `fourierTransform_mstar`, and under the linear operations).

## Main results

* `dense_ccFourierSubalgebra`: **density of `C_c` transforms in `C₀(Ĝ, ℂ)`**, by the
 Stone–Weierstrass theorem for functions vanishing at infinity together with the
 separation (`fourierTransform_separates`) and non-vanishing
 (`exists_fourierTransform_eq_one`) properties of the transform;
* `exists_cc_fourier_close`: the approximation form — every `u ∈ C₀(Ĝ, ℂ)` is within `ε`
 of the transform of some `C_c` function;
* `Continuous.eq_zero_of_forall_integral_cc_eq_zero`: a bounded-continuous-testing lemma on
 a locally compact Hausdorff space carrying an open-positive measure — a continuous
 function integrating to zero against every nonnegative real `C_c` test function vanishes
 identically;
* `measure_ext_of_forall_integral_char_eq`: **uniqueness of Fourier–Stieltjes transforms**:
 two finite positive regular measures on `Ĝ` whose character integrals
 `∫ χ, χ x ∂σ` agree for every `x: G` are equal. The proof combines the Fubini theorem
 of `Pontryagin.Mathlib.FiniteMeasureFubini` (to convert integrals of transforms into transforms
 of the hypothesis), the density theorem, and Mathlib's
 `Measure.ext_of_integral_eq_on_compactlySupported`.
-/

open Filter Function _root_.MeasureTheory Set _root_.Topology
open scoped ComplexConjugate ENNReal ZeroAtInfty CompactlySupported

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.

-- `show` is used to beta-reduce goals and to cross the definitional equality between the
-- bundled `C₀` transform and `fourierTransform`.

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-! ### The `C₀` bundling of `C_c` transforms -/

section CcFourierC0

/-- The Fourier transform of a continuous compactly supported function, bundled as an
element of `C₀(Ĝ, ℂ)`: it is continuous by `continuous_fourierTransform` and vanishes at
infinity by the Riemann–Lebesgue lemma `tendsto_fourierTransform_cocompact`. -/
def PontryaginDual.ccFourierC0 (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    C₀(PontryaginDual G, ℂ) where
  toFun := FourierTransform.PontryaginDual.fourierTransform μ f
  continuous_toFun := FourierTransform.PontryaginDual.continuous_fourierTransform μ (hfc.integrable_of_hasCompactSupport hfs)
  zero_at_infty' :=
    FourierTransform.PontryaginDual.tendsto_fourierTransform_cocompact μ (hfc.integrable_of_hasCompactSupport hfs)

@[simp]
theorem PontryaginDual.coe_ccFourierC0 (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    ⇑(FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs) = FourierTransform.PontryaginDual.fourierTransform μ f :=
  rfl

theorem PontryaginDual.ccFourierC0_apply (f : G → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (χ : PontryaginDual G) : FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs χ = FourierTransform.PontryaginDual.fourierTransform μ f χ :=
  rfl

end CcFourierC0

/-! ### The subalgebra of `C_c` transforms and its density -/

section Subalgebra

/-- The set of Fourier transforms of continuous compactly supported functions, as a
non-unital star subalgebra of `C₀(Ĝ, ℂ)`. Multiplicativity is `fourierTransform_mconv`
(the convolution of two `C_c` functions is again `C_c`), the star operation is
`fourierTransform_mstar`, and the linear structure comes from linearity of the
transform. -/
def PontryaginDual.ccFourierSubalgebra : NonUnitalStarSubalgebra ℂ C₀(PontryaginDual G, ℂ) where
  carrier := {u | ∃ f : G → ℂ, ∃ (hfc : Continuous f) (hfs : HasCompactSupport f),
    u = FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs}
  add_mem' := by
    rintro u v ⟨f, hfc, hfs, rfl⟩ ⟨g, hgc, hgs, rfl⟩
    refine ⟨f + g, hfc.add hgc, hfs.add hgs, ?_⟩
    ext χ
    rw [ZeroAtInftyContinuousMap.add_apply]
    exact (congrFun (FourierTransform.PontryaginDual.fourierTransform_add μ (hfc.integrable_of_hasCompactSupport hfs)
      (hgc.integrable_of_hasCompactSupport hgs)) χ).symm
  zero_mem' := by
    refine ⟨0, continuous_const, HasCompactSupport.zero, ?_⟩
    ext χ
    rw [ZeroAtInftyContinuousMap.zero_apply]
    show (0 : ℂ) = FourierTransform.PontryaginDual.fourierTransform μ (0 : G → ℂ) χ
    rw [FourierTransform.PontryaginDual.fourierTransform_apply]
    simp
  mul_mem' := by
    rintro u v ⟨f, hfc, hfs, rfl⟩ ⟨g, hgc, hgs, rfl⟩
    refine ⟨Convolution.MeasureTheory.mconv μ f g,
      Convolution.Continuous.mconv (μ := μ) hfc hfs hgc hgs,
      Convolution.HasCompactSupport.mconv (μ := μ) hfs hgs, ?_⟩
    ext χ
    rw [ZeroAtInftyContinuousMap.mul_apply]
    exact (FourierTransform.PontryaginDual.fourierTransform_mconv μ hfc hfs hgc hgs χ).symm
  smul_mem' := by
    rintro c u ⟨f, hfc, hfs, rfl⟩
    refine ⟨c • f, hfc.const_smul c, hfs.mono (support_const_smul_subset c f), ?_⟩
    ext χ
    rw [ZeroAtInftyContinuousMap.smul_apply]
    exact (congrFun (FourierTransform.PontryaginDual.fourierTransform_smul μ c f) χ).symm
  star_mem' := by
    rintro u ⟨f, hfc, hfs, rfl⟩
    refine ⟨Convolution.MeasureTheory.mstar f, (Convolution.Continuous.mstar hfc), (Convolution.HasCompactSupport.mstar hfs), ?_⟩
    ext χ
    rw [ZeroAtInftyContinuousMap.star_apply]
    exact (FourierTransform.PontryaginDual.fourierTransform_mstar μ f χ).symm

theorem PontryaginDual.mem_ccFourierSubalgebra_iff {u : C₀(PontryaginDual G, ℂ)} :
    u ∈ FourierDense.PontryaginDual.ccFourierSubalgebra μ ↔
      ∃ f : G → ℂ, ∃ (hfc : Continuous f) (hfs : HasCompactSupport f),
        u = FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs :=
  Iff.rfl

theorem PontryaginDual.ccFourierC0_mem_ccFourierSubalgebra (f : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) : FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs ∈ FourierDense.PontryaginDual.ccFourierSubalgebra μ :=
  ⟨f, hfc, hfs, rfl⟩

/-- **Density of `C_c` Fourier transforms in `C₀(Ĝ, ℂ)`**, by the Stone–Weierstrass theorem
for functions vanishing at infinity: the subalgebra of transforms separates characters
(`fourierTransform_separates`) and vanishes nowhere (`exists_fourierTransform_eq_one`). -/
theorem PontryaginDual.dense_ccFourierSubalgebra :
    Dense (FourierDense.PontryaginDual.ccFourierSubalgebra μ : Set C₀(PontryaginDual G, ℂ)) := by
  refine StoneWeierstrass.ZeroAtInftyContinuousMap.nonUnitalStarSubalgebra_dense_of_separatesPoints
    (FourierDense.PontryaginDual.ccFourierSubalgebra μ) (fun χ χ' hne => ?_) (fun χ => ?_)
  · obtain ⟨f, hfc, hfs, hsep⟩ := Spectrum.PontryaginDual.fourierTransform_separates μ hne
    exact ⟨FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs,
      FourierDense.PontryaginDual.ccFourierC0_mem_ccFourierSubalgebra μ f hfc hfs, hsep⟩
  · obtain ⟨f, hfc, hfs, hone⟩ := Spectrum.PontryaginDual.exists_fourierTransform_eq_one μ χ
    refine ⟨FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs,
      FourierDense.PontryaginDual.ccFourierC0_mem_ccFourierSubalgebra μ f hfc hfs, ?_⟩
    show FourierTransform.PontryaginDual.fourierTransform μ f χ ≠ 0
    rw [hone]
    exact one_ne_zero

/-- Approximation form of the density theorem: every function in `C₀(Ĝ, ℂ)` is within `ε`
of the Fourier transform of a continuous compactly supported function. -/
theorem PontryaginDual.exists_cc_fourier_close (u : C₀(PontryaginDual G, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : G → ℂ, ∃ (hfc : Continuous f) (hfs : HasCompactSupport f),
      ‖FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs - u‖ ≤ ε := by
  obtain ⟨v, hvA, hvu⟩ := Metric.mem_closure_iff.mp (FourierDense.PontryaginDual.dense_ccFourierSubalgebra μ u) ε hε
  obtain ⟨f, hfc, hfs, rfl⟩ := hvA
  refine ⟨f, hfc, hfs, ?_⟩
  rw [← dist_eq_norm, dist_comm]
  exact hvu.le

end Subalgebra

/-! ### Integration of `C₀` functions against finite measures -/

section C0Integration

variable {Y : Type*} [TopologicalSpace Y]

theorem ZeroAtInftyContinuousMap.norm_apply_le (v : C₀(Y, ℂ)) (p : Y) : ‖v p‖ ≤ ‖v‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm v.toBCF p

variable {mY : MeasurableSpace Y} [OpensMeasurableSpace Y]
  (σ : Measure Y) [IsFiniteMeasure σ]

/-- A continuous function vanishing at infinity is integrable against every finite Borel
measure. -/
theorem ZeroAtInftyContinuousMap.integrable (v : C₀(Y, ℂ)) : Integrable (⇑v) σ :=
  (integrable_const ‖v‖).mono' (map_continuous v).aestronglyMeasurable
    (Eventually.of_forall fun p => (FourierDense.ZeroAtInftyContinuousMap.norm_apply_le v) p)

/-- Integration against a finite measure is a continuous functional on `C₀`. -/
theorem MeasureTheory.continuous_integral_zeroAtInfty :
    Continuous fun v : C₀(Y, ℂ) => ∫ p, v p ∂σ := by
  refine (LipschitzWith.of_dist_le_mul (K := (σ Set.univ).toNNReal) fun v w => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖(∫ p, v p ∂σ) - ∫ p, w p ∂σ‖
      = ‖∫ p, (v p - w p) ∂σ‖ := by
        rw [integral_sub
          (FourierDense.ZeroAtInftyContinuousMap.integrable (σ := σ) v)
          (FourierDense.ZeroAtInftyContinuousMap.integrable (σ := σ) w)]
    _ ≤ ∫ _, ‖v - w‖ ∂σ := by
        refine norm_integral_le_of_norm_le (integrable_const _)
          (Eventually.of_forall fun p => ?_)
        rw [← ZeroAtInftyContinuousMap.sub_apply]
        exact (FourierDense.ZeroAtInftyContinuousMap.norm_apply_le (v - w)) p
    _ = σ.real Set.univ * ‖v - w‖ := by rw [integral_const, smul_eq_mul]
    _ = ((σ Set.univ).toNNReal : ℝ) * ‖v - w‖ := rfl

end C0Integration

/-! ### Testing a bounded continuous function against nonnegative `C_c` functions -/

section Testing

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Testing lemma**: on a locally compact Hausdorff space carrying an open-positive
measure that is finite on compacts, a continuous function whose integral against every
nonnegative continuous compactly supported real test function vanishes is identically
zero. (No global bound on `u` is needed: the test functions have compact support.) -/
theorem Continuous.eq_zero_of_forall_integral_cc_eq_zero {u : X → ℂ} (hu : Continuous u)
    (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → (∀ x, 0 ≤ f x) →
      ∫ x, f x • u x ∂ν = 0) :
    ∀ x, u x = 0 := by
  intro x₀
  by_contra hne
  have hpos : 0 < ‖u x₀‖ := norm_pos_iff.mpr hne
  -- a neighborhood of `x₀` where `u` is within `‖u x₀‖ / 2` of `u x₀`
  have hVnhds : {x : X | ‖u x - u x₀‖ < ‖u x₀‖ / 2} ∈ nhds x₀ := by
    have hc : Continuous fun x => ‖u x - u x₀‖ := (hu.sub continuous_const).norm
    have h0 : Set.Iio (‖u x₀‖ / 2) ∈ nhds ((fun x => ‖u x - u x₀‖) x₀) := by
      simpa using Iio_mem_nhds (half_pos hpos)
    exact hc.continuousAt.preimage_mem_nhds h0
  obtain ⟨V, hVsub, hVopen, hVx₀⟩ := mem_nhds_iff.mp hVnhds
  -- a compact set between `x₀` and `V`, and a Urysohn bump supported inside it
  obtain ⟨L, hLcomp, hL1, hLV⟩ :=
    exists_compact_between isCompact_singleton hVopen (singleton_subset_iff.mpr hVx₀)
  obtain ⟨g, hg1, hg0, hgs, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact isCompact_singleton
      isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hL1)
  have hgnonneg : ∀ x, 0 ≤ g x := fun x => (hg01 x).1
  have hgsupp : tsupport ⇑g ⊆ {x : X | ‖u x - u x₀‖ < ‖u x₀‖ / 2} := by
    have h1 : support ⇑g ⊆ interior L := fun x hx => by
      by_contra hxL
      exact hx (hg0 hxL)
    exact ((closure_mono h1).trans
      (closure_minimal interior_subset hLcomp.isClosed)).trans (hLV.trans hVsub)
  have hgint : Integrable (⇑g) ν := g.continuous.integrable_of_hasCompactSupport hgs
  have hgpos : 0 < ∫ x, g x ∂ν :=
    integral_pos_of_integrable_nonneg_nonzero (x := x₀) g.continuous hgint
      (fun x => (hg01 x).1) (by rw [hg1 rfl]; exact one_ne_zero)
  -- the tested integral splits as `∫ g • (u - u x₀) + (∫ g) • u x₀`
  have hint1 : Integrable (fun x => g x • (u x - u x₀)) ν :=
    (g.continuous.smul (hu.sub continuous_const)).integrable_of_hasCompactSupport
      hgs.smul_right
  have hint2 : Integrable (fun x => g x • u x₀) ν := hgint.smul_const (u x₀)
  have hsplit : ∫ x, g x • u x ∂ν
      = (∫ x, g x • (u x - u x₀) ∂ν) + (∫ x, g x ∂ν) • u x₀ := by
    rw [← integral_smul_const, ← integral_add hint1 hint2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show g x • u x = g x • (u x - u x₀) + g x • u x₀
    rw [smul_sub, sub_add_cancel]
  have hzero : ∫ x, g x • u x ∂ν = 0 := h ⇑g g.continuous hgs hgnonneg
  have hsum : (∫ x, g x • (u x - u x₀) ∂ν) + (∫ x, g x ∂ν) • u x₀ = 0 := by
    rw [← hsplit]
    exact hzero
  have hneg : (∫ x, g x ∂ν) • u x₀ = -(∫ x, g x • (u x - u x₀) ∂ν) :=
    eq_neg_of_add_eq_zero_left (by rwa [add_comm] at hsum)
  -- the error term is at most `(∫ g) · ‖u x₀‖ / 2`
  have hbound : ‖∫ x, g x • (u x - u x₀) ∂ν‖ ≤ (∫ x, g x ∂ν) * (‖u x₀‖ / 2) := by
    have hpt : ∀ x, ‖g x • (u x - u x₀)‖ ≤ g x * (‖u x₀‖ / 2) := by
      intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hgnonneg x)]
      by_cases hx : x ∈ tsupport ⇑g
      · exact mul_le_mul_of_nonneg_left (hgsupp hx).le (hgnonneg x)
      · rw [image_eq_zero_of_notMem_tsupport hx]
        simp
    refine (norm_integral_le_of_norm_le (hgint.mul_const _)
      (Eventually.of_forall hpt)).trans_eq ?_
    exact integral_mul_const _ _
  -- hence `(∫ g) · ‖u x₀‖ ≤ (∫ g) · ‖u x₀‖ / 2`, a contradiction
  have hfinal : (∫ x, g x ∂ν) * ‖u x₀‖ ≤ (∫ x, g x ∂ν) * (‖u x₀‖ / 2) :=
    calc (∫ x, g x ∂ν) * ‖u x₀‖
        = ‖(∫ x, g x ∂ν) • u x₀‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgpos.le]
      _ = ‖∫ x, g x • (u x - u x₀) ∂ν‖ := by rw [hneg, norm_neg]
      _ ≤ (∫ x, g x ∂ν) * (‖u x₀‖ / 2) := hbound
  have hcontra : ‖u x₀‖ ≤ ‖u x₀‖ / 2 := le_of_mul_le_mul_left hfinal hgpos
  linarith

end Testing

/-! ### Uniqueness of Fourier–Stieltjes transforms -/

variable {mΓ : MeasurableSpace (PontryaginDual G)} [BorelSpace (PontryaginDual G)]

omit [T2Space G] [μ.Regular] in
/-- Integrating a `C_c` Fourier transform against a finite (inner regular) measure on the
dual group computes the `μ`-integral of `f` against the conjugated character integral:

`∫ χ, 𝓕f(χ) ∂σ = ∫ x, f x * conj (∫ χ, χ x ∂σ) ∂μ`.

This is the Fubini step of the Fourier–Stieltjes uniqueness theorem; the iterated-integral
swap is `integral_integral_swap_of_finite_of_compactSupport`, which requires no product
σ-algebra. -/
theorem PontryaginDual.integral_fourierTransform_cc (σ : Measure (PontryaginDual G)) [IsFiniteMeasure σ]
    [σ.InnerRegularCompactLTTop] {f : G → ℂ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) :
    ∫ χ, FourierTransform.PontryaginDual.fourierTransform μ f χ ∂σ = ∫ x, f x * conj (∫ χ, (χ x : ℂ) ∂σ) ∂μ := by
  obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hfs
  -- joint continuity of the kernel `(χ, x) ↦ f x * conj (χ x)`
  have heval : Continuous fun p : PontryaginDual G × G => ((p.1 p.2 : Circle) : ℂ) := by
    change Continuous fun p : (G →ₜ* Circle) × G => ((p.1 p.2 : Circle) : ℂ)
    exact continuous_induced_dom.comp continuous_eval
  have hFc : Continuous (uncurry fun (χ : PontryaginDual G) (x : G) =>
      f x * conj (χ x : ℂ)) :=
    (hfc.comp continuous_snd).mul (Complex.continuous_conj.comp heval)
  have hFb : ∀ (χ : PontryaginDual G) (x : G), ‖f x * conj (χ x : ℂ)‖ ≤ C := by
    intro χ x
    rw [norm_mul, RCLike.norm_conj, Circle.norm_coe, mul_one]
    exact hC x
  have hFsupp : ∀ (χ : PontryaginDual G) (x : G), x ∉ tsupport f →
      f x * conj (χ x : ℂ) = 0 := fun χ x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  calc ∫ χ, FourierTransform.PontryaginDual.fourierTransform μ f χ ∂σ
      = ∫ χ, ∫ x, f x * conj (χ x : ℂ) ∂μ ∂σ := rfl
    _ = ∫ x, ∫ χ, f x * conj (χ x : ℂ) ∂σ ∂μ :=
        FiniteMeasureFubini.MeasureTheory.integral_integral_swap_of_finite_of_compactSupport hFc hFb hfs hFsupp
    _ = ∫ x, f x * conj (∫ χ, (χ x : ℂ) ∂σ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        calc ∫ χ, f x * conj (χ x : ℂ) ∂σ
            = f x * ∫ χ, conj (χ x : ℂ) ∂σ := integral_const_mul _ _
          _ = f x * conj (∫ χ, (χ x : ℂ) ∂σ) := by rw [integral_conj]

include μ in
/-- **Uniqueness of Fourier–Stieltjes transforms.** Two finite positive regular measures
on the Pontryagin dual whose character integrals agree — `∫ χ, χ x ∂σ₁ = ∫ χ, χ x ∂σ₂` for
every `x: G` — are equal.

The proof tests the measures against the Fourier transforms of `C_c` functions (where the
hypothesis enters through `integral_fourierTransform_cc`), extends by density
(`dense_ccFourierSubalgebra`) and continuity of integration to all of `C₀(Ĝ, ℂ)`, and
concludes by Riesz–Markov uniqueness (`Measure.ext_of_integral_eq_on_compactlySupported`)
applied to real compactly supported test functions. -/
theorem PontryaginDual.measure_ext_of_forall_integral_char_eq
    {σ₁ σ₂ : Measure (PontryaginDual G)} [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    [σ₁.Regular] [σ₂.Regular]
    (h : ∀ x : G, ∫ χ, (χ x : ℂ) ∂σ₁ = ∫ χ, (χ x : ℂ) ∂σ₂) : σ₁ = σ₂ := by
  -- Step 1: the two integration functionals agree on the dense subalgebra of transforms.
  have hEqOn : Set.EqOn (fun v : C₀(PontryaginDual G, ℂ) => ∫ χ, v χ ∂σ₁)
      (fun v : C₀(PontryaginDual G, ℂ) => ∫ χ, v χ ∂σ₂)
      (FourierDense.PontryaginDual.ccFourierSubalgebra μ : Set C₀(PontryaginDual G, ℂ)) := by
    intro v hv
    obtain ⟨f, hfc, hfs, rfl⟩ := hv
    show ∫ χ, FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs χ ∂σ₁ = ∫ χ, FourierDense.PontryaginDual.ccFourierC0 μ f hfc hfs χ ∂σ₂
    simp only [FourierDense.PontryaginDual.ccFourierC0_apply]
    rw [FourierDense.PontryaginDual.integral_fourierTransform_cc μ σ₁ hfc hfs, FourierDense.PontryaginDual.integral_fourierTransform_cc μ σ₂ hfc hfs]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show f x * conj (∫ χ, (χ x : ℂ) ∂σ₁) = f x * conj (∫ χ, (χ x : ℂ) ∂σ₂)
    rw [h x]
  -- Step 2: by density and continuity, they agree on all of `C₀(Ĝ, ℂ)`.
  have hfun : (fun v : C₀(PontryaginDual G, ℂ) => ∫ χ, v χ ∂σ₁)
      = fun v : C₀(PontryaginDual G, ℂ) => ∫ χ, v χ ∂σ₂ :=
    Continuous.ext_on (FourierDense.PontryaginDual.dense_ccFourierSubalgebra μ)
      (FourierDense.MeasureTheory.continuous_integral_zeroAtInfty σ₁) (FourierDense.MeasureTheory.continuous_integral_zeroAtInfty σ₂) hEqOn
  -- Step 3: test against real compactly supported functions and apply Riesz–Markov
  -- uniqueness.
  refine MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported fun γ => ?_
  have hγc : Continuous fun χ : PontryaginDual G => ((γ χ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (map_continuous γ)
  have hγs : HasCompactSupport fun χ : PontryaginDual G => ((γ χ : ℝ) : ℂ) :=
    γ.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have h2 : ∫ χ, ((γ χ : ℝ) : ℂ) ∂σ₁ = ∫ χ, ((γ χ : ℝ) : ℂ) ∂σ₂ :=
    congrFun hfun
      { toFun := fun χ => ((γ χ : ℝ) : ℂ)
        continuous_toFun := hγc
        zero_at_infty' := hγs.is_zero_at_infty }
  rw [show ∫ χ, ((γ χ : ℝ) : ℂ) ∂σ₁ = ((∫ χ, γ χ ∂σ₁ : ℝ) : ℂ) from integral_ofReal,
    show ∫ χ, ((γ χ : ℝ) : ℂ) ∂σ₂ = ((∫ χ, γ χ ∂σ₂ : ℝ) : ℂ) from integral_ofReal] at h2
  exact_mod_cast h2

end

end OAI.Topology.Pontryagin.FourierDense
