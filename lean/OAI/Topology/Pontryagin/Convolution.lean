import OAI.Topology.Pontryagin.CcFubini
import OAI.Topology.Pontryagin.Translation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! # Convolution -/

namespace OAI.Topology.Pontryagin.Convolution.MeasureTheory

noncomputable section

open _root_.MeasureTheory

/-!
# Convolution and the star involution on a locally compact abelian group

For a locally compact Hausdorff abelian group `G` with Haar measure `μ`, this file develops the
convolution product

`mconv μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ`

and the involution `mstar f x = conj (f x⁻¹)`, written multiplicatively throughout, for the two
classes of functions used in the proof of Pontryagin duality: continuous compactly supported
functions and `L²` functions.

## Main definitions

* `mconv μ f g`: the convolution `x ↦ ∫ y, f y * g (y⁻¹ * x) ∂μ`;
* `mstar f`: the involution `x ↦ conj (f x⁻¹)`.

## Main results

For `mstar`: interaction with continuity, supports, integrals (`integral_mstar`) and `Lp`
seminorms (`eLpNorm_mstar`, `MemLp.mstar`).

For convolution of continuous compactly supported functions: `Continuous.mconv`,
`HasCompactSupport.mconv`, `tsupport_mconv_subset`, the integral identities
`integral_mconv_eq_mul` and
`integral_norm_mconv_le`, commutativity `mconv_comm`, associativity `mconv_assoc`, and the
interaction with `mstar` and translation (`mstar_mconv`, `mtranslate_mconv`,
`mconv_mtranslate`).

For convolution of `L²` functions: convolution is everywhere defined with the pointwise
Cauchy–Schwarz bound `norm_mconv_le_of_memLp_two`, it is continuous
(`continuous_mconv_of_memLp_two`), it only depends on the a.e. classes (`mconv_congr_ae`), and
`mconv μ f (mstar f) 1 = ∫ ‖f‖²` (`mconv_mstar_self_one`).

All iterated-integral manipulations go through Mathlib's
`integral_integral_swap_of_hasCompactSupport` (with the slice API of
`Pontryagin.Mathlib.CcFubini`); no product
measures or σ-finiteness assumptions are used anywhere.
-/

open Function Set _root_.Topology Filter
open scoped ENNReal Pointwise ComplexConjugate

-- The sections below deliberately use one coarse hypothesis block (locally compact Hausdorff
-- abelian group with regular Haar measure) rather than minimal per-lemma assumptions.

/-! ### The involution `mstar` -/

section MstarDef

variable {G : Type*} [CommGroup G]

/-- The star involution on complex-valued functions on a multiplicative group:
`mstar f x = conj (f x⁻¹)`. -/
def mstar (f : G → ℂ) : G → ℂ := fun x => conj (f x⁻¹)

@[simp]
theorem mstar_apply (f : G → ℂ) (x : G) : mstar f x = conj (f x⁻¹) := rfl

@[simp]
theorem mstar_mstar (f : G → ℂ) : mstar (mstar f) = f := by
  funext x
  simp

end MstarDef

section MstarTopology

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] {f : G → ℂ}

theorem _root_.OAI.Topology.Pontryagin.Convolution.Continuous.mstar (hf : Continuous f) : Continuous (Convolution.MeasureTheory.mstar f) :=
  Complex.continuous_conj.comp (hf.comp continuous_inv)

theorem tsupport_mstar (f : G → ℂ) : tsupport (mstar f) = (tsupport f)⁻¹ := by
  have hsupp : support (mstar f) = (support f)⁻¹ := by
    ext x
    simp only [mem_support, mstar_apply, ne_eq, starRingEnd_apply, star_eq_zero, Set.mem_inv]
  unfold tsupport
  rw [hsupp, ← inv_closure]

theorem _root_.OAI.Topology.Pontryagin.Convolution.HasCompactSupport.mstar (hf : HasCompactSupport f) :
    HasCompactSupport (Convolution.MeasureTheory.mstar f) := by
  have h := IsCompact.inv hf
  rwa [← tsupport_mstar] at h

end MstarTopology

/-! ### Convolution: definition -/

section MconvDef

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

/-- The convolution of two complex-valued functions on a multiplicative group with respect to a
measure `μ`: `mconv μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ`. -/
def mconv (μ : Measure G) (f g : G → ℂ) : G → ℂ := fun x => ∫ y, f y * g (y⁻¹ * x) ∂μ

theorem mconv_apply (μ : Measure G) (f g : G → ℂ) (x : G) :
    mconv μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ := rfl

end MconvDef

/-! ### The convolution kernel `(x, y) ↦ f y * g (y⁻¹ * x)` -/

section Kernel

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  {f g : G → ℂ}

omit [T2Space G] in
/-- The convolution kernel of two continuous functions is continuous. -/
theorem mconv_kernel_continuous (hf : Continuous f) (hg : Continuous g) :
    Continuous (uncurry fun x y : G => f y * g (y⁻¹ * x)) :=
  (hf.comp continuous_snd).mul (hg.comp (continuous_snd.inv.mul continuous_fst))

omit [IsTopologicalGroup G] [T2Space G] in
/-- The convolution kernel of `f` and `g` is supported in
`(tsupport f * tsupport g) ×ˢ tsupport f`. -/
theorem mconv_kernel_support_subset :
    support (uncurry fun x y : G => f y * g (y⁻¹ * x)) ⊆
      (tsupport f * tsupport g) ×ˢ tsupport f := by
  rintro ⟨x, y⟩ hp
  have hp' : f y * g (y⁻¹ * x) ≠ 0 := hp
  have h1 : y ∈ tsupport f := subset_tsupport f (mem_support.mpr (left_ne_zero_of_mul hp'))
  have h2 : y⁻¹ * x ∈ tsupport g :=
    subset_tsupport g (mem_support.mpr (right_ne_zero_of_mul hp'))
  refine Set.mem_prod.mpr ⟨?_, h1⟩
  have h3 := Set.mul_mem_mul h1 h2
  rwa [mul_inv_cancel_left] at h3

omit [T2Space G] in
/-- The convolution kernel of two compactly supported functions is compactly supported. -/
private theorem mconv_kernel_hasCompactSupport (hf' : HasCompactSupport f)
    (hg' : HasCompactSupport g) :
    HasCompactSupport (uncurry fun x y : G => f y * g (y⁻¹ * x)) :=
  HasCompactSupport.of_support_subset_isCompact
    ((hf'.isCompact.mul hg'.isCompact).prod hf'.isCompact) mconv_kernel_support_subset

end Kernel

/-! ### Convolution and `mstar` on a locally compact abelian group with Haar measure -/

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-! #### `mstar`, measures and integrals -/

omit [T2Space G] in
theorem integral_mstar (f : G → ℂ) : ∫ x, mstar f x ∂μ = conj (∫ x, f x ∂μ) :=
  (integral_inv_eq_self (fun x => conj (f x)) μ).trans integral_conj

omit [T2Space G] in
/-- The map `y ↦ y⁻¹ * x` preserves any regular Haar measure on an abelian group. -/
theorem measurePreserving_inv_mul (x : G) : MeasurePreserving (fun y => y⁻¹ * x) μ μ :=
  (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)

omit [T2Space G] in
theorem eLpNorm_comp_inv {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {f : G → E}
    (hf : AEStronglyMeasurable f μ) : eLpNorm (fun x => f x⁻¹) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving hf (Measure.measurePreserving_inv μ)

omit [T2Space G] in
theorem MemLp.comp_inv {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {f : G → E}
    (hf : MemLp f p μ) : MemLp (fun x => f x⁻¹) p μ :=
  hf.comp_measurePreserving (Measure.measurePreserving_inv μ)

omit [T2Space G] in
theorem eLpNorm_mstar {p : ℝ≥0∞} {f : G → ℂ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (mstar f) p μ = eLpNorm f p μ :=
  by
    change eLpNorm (star (fun x => f x⁻¹)) p μ = _
    rw [eLpNorm_star, eLpNorm_comp_inv μ hf]

omit [T2Space G] in
theorem MemLp.mstar {p : ℝ≥0∞} {f : G → ℂ} (hf : MemLp f p μ) :
    MemLp (Convolution.MeasureTheory.mstar f) p μ :=
  by
    change eLpNorm (Convolution.MeasureTheory.mstar f) p μ < ∞
    rw [eLpNorm_mstar μ hf.aestronglyMeasurable]
    exact hf

omit [T2Space G] in
theorem eLpNorm_shift {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {g : G → E}
    (hg : AEStronglyMeasurable g μ) (x : G) :
    eLpNorm (fun y => g (y⁻¹ * x)) p μ = eLpNorm g p μ :=
  eLpNorm_comp_measurePreserving hg (measurePreserving_inv_mul μ x)

omit [T2Space G] in
theorem MemLp.shift {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {g : G → E}
    (hg : MemLp g p μ) (x : G) : MemLp (fun y => g (y⁻¹ * x)) p μ :=
  hg.comp_measurePreserving (measurePreserving_inv_mul μ x)

omit [T2Space G] in
/-- For `g ∈ L²`, the shifted function `y ↦ g (y⁻¹ * x)` is again in `L²`. -/
theorem memLp_two_shift {g : G → ℂ} (hg : MemLp g 2 μ) (x : G) :
    MemLp (fun y => g (y⁻¹ * x)) 2 μ :=
  Convolution.MeasureTheory.MemLp.shift (μ := μ) hg x

omit [T2Space G] in
/-- Shifting `y ↦ g (y⁻¹ * x)` preserves the `L²` norm. -/
theorem eLpNorm_two_shift {g : G → ℂ} (hg : MemLp g 2 μ) (x : G) :
    eLpNorm (fun y => g (y⁻¹ * x)) 2 μ = eLpNorm g 2 μ :=
  eLpNorm_shift μ hg.aestronglyMeasurable x

omit [T2Space G] in
/-- Convolution only depends on the almost-everywhere classes of its arguments, pointwise. -/
theorem mconv_congr_ae {f f' g g' : G → ℂ} (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    mconv μ f g = mconv μ f' g' := by
  funext x
  refine integral_congr_ae ?_
  have h : (fun y => g (y⁻¹ * x)) =ᵐ[μ] fun y => g' (y⁻¹ * x) :=
    (measurePreserving_inv_mul μ x).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hf, h] with y hy1 hy2
  exact congrArg₂ (· * ·) hy1 hy2

/-! #### The fundamental integral identity for the convolution kernel -/

omit [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
/-- For continuous compactly supported `f g: G → ℂ`,
`∫ x ∫ y, f y * g (y⁻¹ x) = (∫ f) * (∫ g)`. -/
private theorem integral_integral_mconv_kernel {f g : G → ℂ}
    (hf : Continuous f) (hf' : HasCompactSupport f)
    (hg : Continuous g) (hg' : HasCompactSupport g) :
    ∫ x, ∫ y, f y * g (y⁻¹ * x) ∂μ ∂μ = (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
  refine (integral_integral_swap_of_hasCompactSupport
    (mconv_kernel_continuous hf hg) (mconv_kernel_hasCompactSupport hf' hg')).trans ?_
  calc ∫ y, ∫ x, f y * g (y⁻¹ * x) ∂μ ∂μ
      = ∫ y, f y * ∫ x, g x ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        change ∫ x, f y * g (y⁻¹ * x) ∂μ = f y * ∫ x, g x ∂μ
        rw [integral_const_mul, integral_mul_left_eq_self g y⁻¹]
    _ = (∫ x, f x ∂μ) * ∫ x, g x ∂μ := integral_mul_const _ f

/-! #### Convolution of continuous compactly supported functions -/

variable {f g h : G → ℂ}

omit [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
/-- The convolution of two continuous compactly supported functions is continuous. -/
theorem _root_.OAI.Topology.Pontryagin.Convolution.Continuous.mconv (hf : Continuous f) (hf' : HasCompactSupport f)
    (hg : Continuous g) (hg' : HasCompactSupport g) : Continuous (Convolution.MeasureTheory.mconv μ f g) :=
  CcFubini.MeasureTheory.continuous_integral_right (mconv_kernel_continuous hf hg)
    (mconv_kernel_hasCompactSupport hf' hg')

omit [T2Space G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The convolution of two compactly supported functions is compactly supported. -/
theorem _root_.OAI.Topology.Pontryagin.Convolution.HasCompactSupport.mconv (hf' : HasCompactSupport f) (hg' : HasCompactSupport g) :
    HasCompactSupport (Convolution.MeasureTheory.mconv μ f g) :=
  CcFubini.MeasureTheory.hasCompactSupport_integral_right (mconv_kernel_hasCompactSupport hf' hg')

omit [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- The support of a convolution is contained in the product of the supports. -/
theorem tsupport_mconv_subset (hf' : HasCompactSupport f) (hg' : HasCompactSupport g) :
    tsupport (mconv μ f g) ⊆ tsupport f * tsupport g := by
  refine closure_minimal (fun x hx => ?_) (hf'.isCompact.mul hg'.isCompact).isClosed
  by_contra hxmem
  have hzero : ∀ y, f y * g (y⁻¹ * x) = 0 := fun y => by
    by_contra hy
    refine hxmem ?_
    have h1 : y ∈ tsupport f := subset_tsupport f (mem_support.mpr (left_ne_zero_of_mul hy))
    have h2 : y⁻¹ * x ∈ tsupport g :=
      subset_tsupport g (mem_support.mpr (right_ne_zero_of_mul hy))
    have h3 := Set.mul_mem_mul h1 h2
    rwa [mul_inv_cancel_left] at h3
  exact hx (by simp [mconv_apply, hzero])

omit [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
/-- `∫ (f ⋆ g) = (∫ f) * (∫ g)` for continuous compactly supported functions. -/
theorem integral_mconv_eq_mul (hf : Continuous f) (hf' : HasCompactSupport f)
    (hg : Continuous g) (hg' : HasCompactSupport g) :
    ∫ x, mconv μ f g x ∂μ = (∫ x, f x ∂μ) * ∫ x, g x ∂μ :=
  integral_integral_mconv_kernel μ hf hf' hg hg'

omit [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
/-- The `L¹`-norm bound `‖f ⋆ g‖₁ ≤ ‖f‖₁ * ‖g‖₁` for continuous compactly supported
functions. -/
theorem integral_norm_mconv_le (hf : Continuous f) (hf' : HasCompactSupport f)
    (hg : Continuous g) (hg' : HasCompactSupport g) :
    ∫ x, ‖mconv μ f g x‖ ∂μ ≤ (∫ x, ‖f x‖ ∂μ) * ∫ x, ‖g x‖ ∂μ := by
  have hFc : Continuous (uncurry fun x y : G => ‖f y * g (y⁻¹ * x)‖) :=
    (mconv_kernel_continuous hf hg).norm
  have hFsupp : HasCompactSupport (uncurry fun x y : G => ‖f y * g (y⁻¹ * x)‖) :=
    (mconv_kernel_hasCompactSupport hf' hg').norm
  have h1 : Integrable (fun x => ‖mconv μ f g x‖) μ :=
    ((Convolution.Continuous.mconv (μ := μ) hf hf' hg hg').integrable_of_hasCompactSupport (Convolution.HasCompactSupport.mconv (μ := μ) hf' hg')).norm
  have h2 : Integrable (fun x => ∫ y, ‖f y * g (y⁻¹ * x)‖ ∂μ) μ :=
    CcFubini.MeasureTheory.integrable_integral_right hFc hFsupp
  have h3 : ∀ x, ‖mconv μ f g x‖ ≤ ∫ y, ‖f y * g (y⁻¹ * x)‖ ∂μ := fun x =>
    norm_integral_le_integral_norm _
  calc ∫ x, ‖mconv μ f g x‖ ∂μ
      ≤ ∫ x, ∫ y, ‖f y * g (y⁻¹ * x)‖ ∂μ ∂μ := integral_mono h1 h2 h3
    _ = ∫ y, ∫ x, ‖f y * g (y⁻¹ * x)‖ ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hFc hFsupp
    _ = ∫ y, ‖f y‖ * ∫ x, ‖g x‖ ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        change ∫ x, ‖f y * g (y⁻¹ * x)‖ ∂μ = ‖f y‖ * ∫ x, ‖g x‖ ∂μ
        calc ∫ x, ‖f y * g (y⁻¹ * x)‖ ∂μ
            = ∫ x, ‖f y‖ * ‖g (y⁻¹ * x)‖ ∂μ := by
              refine integral_congr_ae (Eventually.of_forall fun x => ?_)
              exact norm_mul _ _
          _ = ‖f y‖ * ∫ x, ‖g (y⁻¹ * x)‖ ∂μ := integral_const_mul _ _
          _ = ‖f y‖ * ∫ x, ‖g x‖ ∂μ := by
              rw [integral_mul_left_eq_self (fun x => ‖g x‖) y⁻¹]
    _ = (∫ x, ‖f x‖ ∂μ) * ∫ x, ‖g x‖ ∂μ := integral_mul_const _ _

omit [T2Space G] in
/-- Convolution is commutative. -/
theorem mconv_comm (f g : G → ℂ) : mconv μ f g = mconv μ g f := by
  funext x
  refine Eq.trans (integral_div_left_eq_self (fun y => f y * g (y⁻¹ * x)) μ x).symm ?_
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [div_eq_mul_inv, mul_comm]

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- Convolution of continuous compactly supported functions is associative.

(The compact-support hypothesis for `h` is included for a symmetric API.) -/
theorem mconv_assoc (hf : Continuous f) (hf' : HasCompactSupport f)
    (hg : Continuous g) (hg' : HasCompactSupport g)
    (hh : Continuous h) (_hh' : HasCompactSupport h) :
    mconv μ (mconv μ f g) h = mconv μ f (mconv μ g h) := by
  funext x
  have hKc : Continuous (uncurry fun z y : G => f y * g (y⁻¹ * z) * h (z⁻¹ * x)) :=
    ((hf.comp continuous_snd).mul (hg.comp (continuous_snd.inv.mul continuous_fst))).mul
      (hh.comp (continuous_fst.inv.mul continuous_const))
  have hKsupp : HasCompactSupport (uncurry fun z y : G => f y * g (y⁻¹ * z) * h (z⁻¹ * x)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((hf'.isCompact.mul hg'.isCompact).prod hf'.isCompact) fun p hp => ?_
    have hp' : f p.2 * g (p.2⁻¹ * p.1) ≠ 0 := left_ne_zero_of_mul hp
    exact mconv_kernel_support_subset hp'
  calc mconv μ (mconv μ f g) h x
      = ∫ z, (∫ y, f y * g (y⁻¹ * z) ∂μ) * h (z⁻¹ * x) ∂μ := rfl
    _ = ∫ z, ∫ y, f y * g (y⁻¹ * z) * h (z⁻¹ * x) ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ y, ∫ z, f y * g (y⁻¹ * z) * h (z⁻¹ * x) ∂μ ∂μ :=
        integral_integral_swap_of_hasCompactSupport hKc hKsupp
    _ = ∫ y, f y * ∫ z, g z * h (z⁻¹ * (y⁻¹ * x)) ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        calc ∫ z, f y * g (y⁻¹ * z) * h (z⁻¹ * x) ∂μ
            = ∫ z, f y * (g (y⁻¹ * z) * h (z⁻¹ * x)) ∂μ := by simp_rw [mul_assoc]
          _ = f y * ∫ z, g (y⁻¹ * z) * h (z⁻¹ * x) ∂μ := integral_const_mul _ _
          _ = f y * ∫ z, g z * h (z⁻¹ * (y⁻¹ * x)) ∂μ := by
              refine congrArg (f y * ·) ?_
              refine Eq.trans
                (integral_mul_left_eq_self (fun z => g (y⁻¹ * z) * h (z⁻¹ * x)) y).symm ?_
              refine integral_congr_ae (Eventually.of_forall fun z => ?_)
              simp [mul_assoc]
    _ = mconv μ f (mconv μ g h) x := rfl

omit [T2Space G] in
/-- `mstar` is an anti-involution for convolution; by commutativity, it simply distributes. -/
theorem mstar_mconv (f g : G → ℂ) : mstar (mconv μ f g) = mconv μ (mstar f) (mstar g) := by
  funext x
  calc mstar (mconv μ f g) x
      = conj (∫ y, f y * g (y⁻¹ * x⁻¹) ∂μ) := rfl
    _ = ∫ y, conj (f y * g (y⁻¹ * x⁻¹)) ∂μ := integral_conj.symm
    _ = ∫ y, conj (f y⁻¹ * g ((y⁻¹)⁻¹ * x⁻¹)) ∂μ :=
        (integral_inv_eq_self (fun y => conj (f y * g (y⁻¹ * x⁻¹))) μ).symm
    _ = ∫ y, mstar f y * mstar g (y⁻¹ * x) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [mul_comm]

omit [LocallyCompactSpace G] [T2Space G] [μ.Regular] in
/-- Translation acts on convolutions through the left factor. -/
theorem mtranslate_mconv (a : G) (f g : G → ℂ) :
    Translation.MeasureTheory.mtranslate a (mconv μ f g) = mconv μ (Translation.MeasureTheory.mtranslate a f) g := by
  funext x
  calc Translation.MeasureTheory.mtranslate a (mconv μ f g) x
      = ∫ y, f y * g (y⁻¹ * (a⁻¹ * x)) ∂μ := rfl
    _ = ∫ y, f (a⁻¹ * (a * y)) * g ((a * y)⁻¹ * x) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [mul_assoc]
    _ = ∫ y, f (a⁻¹ * y) * g (y⁻¹ * x) ∂μ :=
        integral_mul_left_eq_self (fun y => f (a⁻¹ * y) * g (y⁻¹ * x)) a
    _ = mconv μ (Translation.MeasureTheory.mtranslate a f) g x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- Translation acts on convolutions through the right factor. -/
theorem mconv_mtranslate (a : G) (f g : G → ℂ) :
    Translation.MeasureTheory.mtranslate a (mconv μ f g) = mconv μ f (Translation.MeasureTheory.mtranslate a g) := by
  funext x
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change f y * g (y⁻¹ * (a⁻¹ * x)) = f y * Translation.MeasureTheory.mtranslate a g (y⁻¹ * x)
  rw [Translation.MeasureTheory.mtranslate_apply, mul_left_comm y⁻¹ a⁻¹ x]

/-! #### Convolution of `L²` functions -/

omit [T2Space G] in
/-- The convolution of two `L²` functions, evaluated at `x`, is the `L²` inner product of
`star f` and the translate by `x` of `y ↦ g y⁻¹`. -/
private theorem mconv_apply_eq_inner {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (x : G) :
    mconv μ f g x = inner ℂ (MemLp.toLp (star f) hf.star)
      (Translation.MeasureTheory.translateLp μ 2 x (MemLp.toLp (fun y => g y⁻¹) (Convolution.MeasureTheory.MemLp.comp_inv (μ := μ) hg))) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  have hu := MemLp.coeFn_toLp hf.star
  have hv0 := MemLp.coeFn_toLp (Convolution.MeasureTheory.MemLp.comp_inv (μ := μ) hg)
  have hv1 := Translation.MeasureTheory.coeFn_translateLp μ 2 x (MemLp.toLp (fun y => g y⁻¹) (Convolution.MeasureTheory.MemLp.comp_inv (μ := μ) hg))
  have hv2 : Translation.MeasureTheory.mtranslate x ⇑(MemLp.toLp (fun y => g y⁻¹) (Convolution.MeasureTheory.MemLp.comp_inv (μ := μ) hg))
      =ᵐ[μ] Translation.MeasureTheory.mtranslate x fun y => g y⁻¹ :=
    (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp hv0
  filter_upwards [hu, hv1.trans hv2] with y hy1 hy2
  rw [RCLike.inner_apply, hy1, hy2]
  simp only [Translation.MeasureTheory.mtranslate_apply, Pi.star_apply, RCLike.star_def, RCLike.conj_conj,
    mul_inv_rev, inv_inv]
  exact mul_comm _ _

omit [T2Space G] in
/-- Pointwise Cauchy–Schwarz bound for the convolution of two `L²` functions. -/
theorem norm_mconv_le_of_memLp_two {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (x : G) :
    ‖mconv μ f g x‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  rw [mconv_apply_eq_inner μ hf hg x]
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
  rw [Translation.MeasureTheory.norm_translateLp, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_star, eLpNorm_comp_inv μ hg.aestronglyMeasurable]

omit [T2Space G] in
/-- The convolution of two `L²` functions is continuous. -/
theorem continuous_mconv_of_memLp_two {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Continuous (mconv μ f g) := by
  have key : mconv μ f g = fun x => inner ℂ (MemLp.toLp (star f) hf.star)
      (Translation.MeasureTheory.translateLp μ 2 x (MemLp.toLp (fun y => g y⁻¹) (Convolution.MeasureTheory.MemLp.comp_inv (μ := μ) hg))) :=
    funext fun x => mconv_apply_eq_inner μ hf hg x
  rw [key]
  exact continuous_const.inner
    (Translation.MeasureTheory.continuous_translateLp μ 2 ENNReal.ofNat_ne_top
      (MemLp.toLp (fun y => g y⁻¹) (Convolution.MeasureTheory.MemLp.comp_inv (μ := μ) hg)))

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [BorelSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- At the identity, `f ⋆ (mstar f)` is the squared `L²` norm of `f`. -/
theorem mconv_mstar_self_one (f : G → ℂ) :
    mconv μ f (mstar f) 1 = ((∫ y, ‖f y‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hpt : ∀ y : G, f y * mstar f (y⁻¹ * 1) = ((‖f y‖ ^ 2 : ℝ) : ℂ) := fun y => by
    rw [mstar_apply, mul_one, inv_inv, RCLike.mul_conj]
    norm_cast
  calc mconv μ f (mstar f) 1
      = ∫ y, ((‖f y‖ ^ 2 : ℝ) : ℂ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        exact hpt y
    _ = ((∫ y, ‖f y‖ ^ 2 ∂μ : ℝ) : ℂ) := integral_ofReal

end

end OAI.Topology.Pontryagin.Convolution.MeasureTheory
