import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Cc Fubini -/

namespace OAI.Topology.Pontryagin.CcFubini

open _root_.MeasureTheory

/-!
# Fubini for jointly continuous compactly supported kernels

This file fills a gap in Mathlib (general-purpose material with no project-specific content)
and is a candidate for upstreaming.

The measure-theoretic workhorse of the project: for a jointly continuous, compactly supported
kernel `F: X → Y → E` on topological spaces equipped with Borel-compatible measures that are
finite on compact sets, the two iterated Bochner integrals agree:

`∫ x, ∫ y, F x y ∂ν ∂μ = ∫ y, ∫ x, F x y ∂μ ∂ν`.

Crucially, there are **no product-measure, product-σ-algebra, (s/σ-)finiteness, regularity or
second-countability hypotheses**: on a general locally compact abelian group (e.g. the
Pontryagin dual of a compact group, which can fail to be σ-compact), Haar measure is not
s-finite and the usual Fubini theorems do not apply. The swap itself is
Mathlib's `MeasureTheory.integral_integral_swap_of_hasCompactSupport` (used directly
downstream); this file provides the slice lemmas that make iterated integrals of
such kernels usable downstream (convolution of `C_c` functions, approximate identities, the
symmetric measure identity):

* slices `F x` and `fun x ↦ F x y` are continuous, compactly supported, hence integrable;
* the partial integrals `fun x ↦ ∫ y, F x y ∂ν` and `fun y ↦ ∫ x, F x y ∂μ` are continuous
 and compactly supported, hence integrable;
* a sup-norm × measure bound for the iterated integral.

## Main statements

* `HasCompactSupport.uncurry_left`, `HasCompactSupport.uncurry_right`: compact support of
 slices.
* `Continuous.integrable_uncurry_left`, `Continuous.integrable_uncurry_right`: integrability
 of slices.
* `continuous_integral_right`, `hasCompactSupport_integral_right`, `integrable_integral_right`
 (and the `_left` counterparts): the partial integrals are continuous, compactly supported,
 integrable.
* `norm_integral_integral_le_of_support_subset`:
 `‖∫ x, ∫ y, F x y ∂ν ∂μ‖ ≤ C * μ.real K₁ * ν.real K₂` for a kernel bounded by `C` and
 supported in `K₁ ×ˢ K₂`.

Everything is stated typeclass-minimally: `OpensMeasurableSpace` plus
`IsFiniteMeasureOnCompacts` suffice for all integrability statements (no `BorelSpace`, no
regularity), and `R1Space` (weaker than `T2Space`) is all that is needed where supports must
be closed off compact sets. In particular all hypotheses hold for Haar measure on a locally
compact Hausdorff group and, more generally, for any Radon-type measure on a locally compact
Hausdorff space.

A nonnegative real-valued version of the swap needs no separate statement: it is the special
case `E = ℝ` (or follows from `E = ℂ` by taking real parts).
-/

open Function
open scoped ENNReal

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Slices of compactly supported kernels -/

section Slices

variable {E : Type*} [Zero E] {F : X → Y → E}

/-- The left slices `F x` of a compactly supported kernel `F` are compactly supported. -/
theorem HasCompactSupport.uncurry_left [R1Space Y] (x : X)
    (hFsupp : HasCompactSupport (uncurry F)) : HasCompactSupport (F x) :=
  HasCompactSupport.intro (hFsupp.isCompact.image continuous_snd) fun y hy ↦ by
    by_contra h
    have : (x, y) ∈ Function.support (uncurry F) := h
    exact hy (Set.mem_image_of_mem _ (subset_tsupport _ this))

/-- The right slices `fun x ↦ F x y` of a compactly supported kernel `F` are compactly
supported. -/
theorem HasCompactSupport.uncurry_right [R1Space X] (y : Y)
    (hFsupp : HasCompactSupport (uncurry F)) : HasCompactSupport fun x ↦ F x y :=
  HasCompactSupport.intro (hFsupp.isCompact.image continuous_fst) fun x hx ↦ by
    by_contra h
    have : (x, y) ∈ Function.support (uncurry F) := h
    exact hx (Set.mem_image_of_mem _ (subset_tsupport _ this))

/-- A compactly supported kernel is supported in a product of two compact sets, namely the
projections of its topological support. -/
theorem HasCompactSupport.exists_support_subset_prod
    (hFsupp : HasCompactSupport (uncurry F)) :
    ∃ K₁ K₂, IsCompact K₁ ∧ IsCompact K₂ ∧ Function.support (uncurry F) ⊆ K₁ ×ˢ K₂ :=
  ⟨_, _, hFsupp.isCompact.image continuous_fst, hFsupp.isCompact.image continuous_snd,
    (subset_tsupport _).trans Set.subset_prod⟩

end Slices

/-! ### Integrability of slices and partial integrals -/

variable {E : Type*} [NormedAddCommGroup E] {F : X → Y → E}
  {mX : MeasurableSpace X} {mY : MeasurableSpace Y} {μ : Measure X} {ν : Measure Y}

/-- The left slices `F x` of a continuous compactly supported kernel are integrable. -/
theorem Continuous.integrable_uncurry_left [OpensMeasurableSpace Y] [R1Space Y]
    [IsFiniteMeasureOnCompacts ν] (hF : Continuous (uncurry F))
    (hFsupp : HasCompactSupport (uncurry F)) (x : X) :
    Integrable (F x) ν :=
  (hF.uncurry_left x).integrable_of_hasCompactSupport (CcFubini.HasCompactSupport.uncurry_left x hFsupp)

/-- The right slices `fun x ↦ F x y` of a continuous compactly supported kernel are
integrable. -/
theorem Continuous.integrable_uncurry_right [OpensMeasurableSpace X] [R1Space X]
    [IsFiniteMeasureOnCompacts μ] (hF : Continuous (uncurry F))
    (hFsupp : HasCompactSupport (uncurry F)) (y : Y) :
    Integrable (fun x ↦ F x y) μ :=
  (hF.uncurry_right y).integrable_of_hasCompactSupport (CcFubini.HasCompactSupport.uncurry_right y hFsupp)

variable [NormedSpace ℝ E]

/-- The partial integral `fun x ↦ ∫ y, F x y ∂ν` of a continuous compactly supported kernel
is continuous. -/
theorem MeasureTheory.continuous_integral_right [OpensMeasurableSpace Y] [IsFiniteMeasureOnCompacts ν]
    (hF : Continuous (uncurry F)) (hFsupp : HasCompactSupport (uncurry F)) :
    Continuous fun x ↦ ∫ y, F x y ∂ν := by
  rw [← continuousOn_univ]
  refine continuousOn_integral_of_compact_support (hFsupp.isCompact.image continuous_snd)
    hF.continuousOn fun p y _ hy ↦ ?_
  by_contra h
  have : (p, y) ∈ Function.support (uncurry F) := h
  exact hy (Set.mem_image_of_mem _ (subset_tsupport _ this))

/-- The partial integral `fun y ↦ ∫ x, F x y ∂μ` of a continuous compactly supported kernel
is continuous. -/
theorem MeasureTheory.continuous_integral_left [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    (hF : Continuous (uncurry F)) (hFsupp : HasCompactSupport (uncurry F)) :
    Continuous fun y ↦ ∫ x, F x y ∂μ := by
  rw [← continuousOn_univ]
  refine continuousOn_integral_of_compact_support (f := fun y x ↦ F x y)
    (hFsupp.isCompact.image continuous_fst) (hF.comp continuous_swap).continuousOn
    fun q x _ hx ↦ ?_
  by_contra h
  have : (x, q) ∈ Function.support (uncurry F) := h
  exact hx (Set.mem_image_of_mem _ (subset_tsupport _ this))

/-- The partial integral `fun x ↦ ∫ y, F x y ∂ν` of a compactly supported kernel is compactly
supported. -/
theorem MeasureTheory.hasCompactSupport_integral_right [R1Space X]
    (hFsupp : HasCompactSupport (uncurry F)) :
    HasCompactSupport fun x ↦ ∫ y, F x y ∂ν :=
  HasCompactSupport.intro (hFsupp.isCompact.image continuous_fst) fun x hx ↦ by
    have h : ∀ y, F x y = 0 := fun y ↦ by
      by_contra h
      have : (x, y) ∈ Function.support (uncurry F) := h
      exact hx (Set.mem_image_of_mem _ (subset_tsupport _ this))
    simp [h]

/-- The partial integral `fun y ↦ ∫ x, F x y ∂μ` of a compactly supported kernel is compactly
supported. -/
theorem MeasureTheory.hasCompactSupport_integral_left [R1Space Y]
    (hFsupp : HasCompactSupport (uncurry F)) :
    HasCompactSupport fun y ↦ ∫ x, F x y ∂μ :=
  HasCompactSupport.intro (hFsupp.isCompact.image continuous_snd) fun y hy ↦ by
    have h : ∀ x, F x y = 0 := fun x ↦ by
      by_contra h
      have : (x, y) ∈ Function.support (uncurry F) := h
      exact hy (Set.mem_image_of_mem _ (subset_tsupport _ this))
    simp [h]

/-- The partial integral `fun x ↦ ∫ y, F x y ∂ν` of a continuous compactly supported kernel
is integrable; in particular the iterated integral `∫ x, ∫ y, F x y ∂ν ∂μ` makes sense. -/
theorem MeasureTheory.integrable_integral_right [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    [R1Space X] [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hF : Continuous (uncurry F)) (hFsupp : HasCompactSupport (uncurry F)) :
    Integrable (fun x ↦ ∫ y, F x y ∂ν) μ :=
  (CcFubini.MeasureTheory.continuous_integral_right hF hFsupp).integrable_of_hasCompactSupport
    (CcFubini.MeasureTheory.hasCompactSupport_integral_right hFsupp)

/-- The partial integral `fun y ↦ ∫ x, F x y ∂μ` of a continuous compactly supported kernel
is integrable; in particular the iterated integral `∫ y, ∫ x, F x y ∂μ ∂ν` makes sense. -/
theorem MeasureTheory.integrable_integral_left [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    [R1Space Y] [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hF : Continuous (uncurry F)) (hFsupp : HasCompactSupport (uncurry F)) :
    Integrable (fun y ↦ ∫ x, F x y ∂μ) ν :=
  (CcFubini.MeasureTheory.continuous_integral_left hF hFsupp).integrable_of_hasCompactSupport
    (CcFubini.MeasureTheory.hasCompactSupport_integral_left hFsupp)

omit [TopologicalSpace X] [TopologicalSpace Y] in
/-- Sup-norm × measure bound for an iterated integral: if a kernel is bounded by `C` and
supported in `K₁ ×ˢ K₂` with `μ K₁` and `ν K₂` finite, then
`‖∫ x, ∫ y, F x y ∂ν ∂μ‖ ≤ C * μ.real K₁ * ν.real K₂`.

No topological hypotheses are needed; recall `μ.real s = (μ s).toReal`. -/
theorem MeasureTheory.norm_integral_integral_le_of_support_subset {K₁ : Set X} {K₂ : Set Y}
    (h₁ : μ K₁ ≠ ∞) (h₂ : ν K₂ ≠ ∞)
    (hsupp : Function.support (uncurry F) ⊆ K₁ ×ˢ K₂) {C : ℝ} (hC : ∀ x y, ‖F x y‖ ≤ C) :
    ‖∫ x, ∫ y, F x y ∂ν ∂μ‖ ≤ C * μ.real K₁ * ν.real K₂ := by
  have h₀ : ∀ x y, x ∉ K₁ ∨ y ∉ K₂ → F x y = 0 := by
    intro x y hxy
    by_contra h
    have hs : (x, y) ∈ Function.support (uncurry F) := h
    rcases hxy with hx | hy
    · exact hx (hsupp hs).1
    · exact hy (hsupp hs).2
  have hinner : ∀ x, ‖∫ y, F x y ∂ν‖ ≤ C * ν.real K₂ := fun x ↦ by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ h₀ x y (Or.inr hy)]
    exact norm_setIntegral_le_of_norm_le_const h₂.lt_top fun y _ ↦ hC x y
  have houter : ∀ x ∉ K₁, (∫ y, F x y ∂ν) = 0 := fun x hx ↦ by
    have h : ∀ y, F x y = 0 := fun y ↦ h₀ x y (Or.inl hx)
    simp [h]
  calc ‖∫ x, ∫ y, F x y ∂ν ∂μ‖
      = ‖∫ x in K₁, ∫ y, F x y ∂ν ∂μ‖ := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero houter]
    _ ≤ C * ν.real K₂ * μ.real K₁ :=
        norm_setIntegral_le_of_norm_le_const h₁.lt_top fun x _ ↦ hinner x
    _ = C * μ.real K₁ * ν.real K₂ := by ring

end OAI.Topology.Pontryagin.CcFubini
