import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.UrysohnsLemma
import OAI.Topology.Pontryagin.CcFubini

/-! # Finite Measure Fubini -/

namespace OAI.Topology.Pontryagin.FiniteMeasureFubini.MeasureTheory

open _root_.MeasureTheory

/-!
# Fubini for kernels compactly supported in one variable, against a finite measure

This file fills a gap in Mathlib (general-purpose material with no project-specific content)
and is a candidate for upstreaming.

Mathlib's `integral_integral_swap_of_hasCompactSupport` swaps iterated integrals of jointly
continuous kernels that are compactly supported *in both variables*. This file extends the
swap to bounded jointly
continuous kernels `F: X → Y → E` that are compactly supported in only **one** variable (the
`y`-variable, say), integrated in the other variable against a **finite inner regular**
measure `σ`:

`∫ x, ∫ y, F x y ∂ν ∂σ = ∫ y, ∫ x, F x y ∂σ ∂ν`.

This is the form of Fubini needed for the symmetric-measure identity of Pontryagin duality:
there the kernel `(x, χ) ↦ f(x) χ(x) g(χ)` on `G × Ĝ` is compactly supported in `x` only,
but the character-space integration happens against finite (regular) measures.

As before there are **no product-measure or product-σ-algebra hypotheses**: the proof
truncates the kernel by Urysohn cutoffs `φ n` equal to `1` on an increasing sequence of
compact sets that exhausts `σ` (inner regularity), applies the compactly supported swap
to each truncation `φ n x • F x y`, and passes to the limit on both
sides by dominated convergence.

## Main statements

* `integral_integral_swap_of_finite_of_compactSupport`: the iterated-integral swap for a
 bounded continuous kernel vanishing for `y` outside a compact set, with `σ` a finite
 measure on `X` that is inner regular on finite-measure sets.
* `continuous_integral_right_of_forall_compl_eq_zero`,
 `continuous_integral_left_of_forall_compl_eq_zero`: the partial integral of a jointly
 continuous kernel compactly supported in the *integrated* variable only is continuous
 in the remaining variable.

## Implementation notes

The inner-regularity hypothesis is stated as `σ.InnerRegularCompactLTTop` (inner regularity
on measurable sets of finite measure with respect to compact sets), which is weaker than
`σ.InnerRegular`; the instance `[σ.InnerRegular] → σ.InnerRegularCompactLTTop` makes the
theorem directly applicable to inner regular measures. The hypotheses `[T2Space X]`,
`[LocallyCompactSpace X]` provide the Urysohn cutoffs (`RegularSpace X` is automatic there),
and `[R1Space Y]` ensures `closure K` is compact, so that the truncated kernels are honestly
compactly supported on `X × Y`. All hypotheses hold in the intended applications, where `X`
and `Y` are locally compact Hausdorff groups and `σ` is a finite Radon-type measure.
-/

open Filter Function Set
open scoped ENNReal _root_.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {μ σ : Measure X} {ν : Measure Y} {F : X → Y → E}

/-! ### Continuity of partial integrals -/

/-- If a jointly continuous kernel `F: X → Y → E` vanishes for `y` outside a fixed compact
set, then the partial integral `fun x ↦ ∫ y, F x y ∂ν` is continuous. Compared with
`continuous_integral_right`, compact support is required only in the integrated variable. -/
theorem continuous_integral_right_of_forall_compl_eq_zero
    [OpensMeasurableSpace Y] [IsFiniteMeasureOnCompacts ν]
    (hF : Continuous (uncurry F)) {K : Set Y} (hK : IsCompact K)
    (hsupp : ∀ x y, y ∉ K → F x y = 0) :
    Continuous fun x ↦ ∫ y, F x y ∂ν := by
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support hK hF.continuousOn
    fun x y _ hy ↦ hsupp x y hy

/-- If a jointly continuous kernel `F: X → Y → E` vanishes for `x` outside a fixed compact
set, then the partial integral `fun y ↦ ∫ x, F x y ∂μ` is continuous. Compared with
`continuous_integral_left`, compact support is required only in the integrated variable. -/
theorem continuous_integral_left_of_forall_compl_eq_zero
    [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    (hF : Continuous (uncurry F)) {K : Set X} (hK : IsCompact K)
    (hsupp : ∀ x y, x ∉ K → F x y = 0) :
    Continuous fun y ↦ ∫ x, F x y ∂μ := by
  rw [← continuousOn_univ]
  exact continuousOn_integral_of_compact_support (f := fun y x ↦ F x y) hK
    (hF.comp continuous_swap).continuousOn fun y x _ hx ↦ hsupp x y hx

/-! ### The iterated-integral swap -/

/-- **Fubini for bounded continuous kernels compactly supported in one variable, against a
finite inner regular measure.** Let `F: X → Y → E` be a bounded jointly continuous kernel
vanishing for `y` outside a compact set `K`. If `σ` is a finite measure on `X` that is inner
regular (for finite-measure sets, with respect to compact sets) and `ν` is finite on compact
sets, then the iterated integrals agree:

`∫ x, ∫ y, F x y ∂ν ∂σ = ∫ y, ∫ x, F x y ∂σ ∂ν`.

There are **no** product-measure, product-σ-algebra, s-finiteness or second-countability
hypotheses; compact support in the `x`-variable is replaced by finiteness and inner
regularity of `σ`. -/
theorem integral_integral_swap_of_finite_of_compactSupport
    [T2Space X] [LocallyCompactSpace X] [R1Space Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    [IsFiniteMeasure σ] [σ.InnerRegularCompactLTTop] [IsFiniteMeasureOnCompacts ν]
    (hF : Continuous (uncurry F)) {C : ℝ} (hC : ∀ x y, ‖F x y‖ ≤ C)
    {K : Set Y} (hK : IsCompact K) (hsupp : ∀ x y, y ∉ K → F x y = 0) :
    ∫ x, ∫ y, F x y ∂ν ∂σ = ∫ y, ∫ x, F x y ∂σ ∂ν := by
  -- Step 1: an increasing sequence of compact sets `Ks n` with `σ (Ks n)ᶜ ≤ (n: ℝ≥0∞)⁻¹`.
  have hcpt : ∀ n : ℕ, ∃ L, L ⊆ univ ∧ IsCompact L ∧ σ univ < σ L + (n : ℝ≥0∞)⁻¹ := fun n ↦
    MeasurableSet.univ.exists_isCompact_lt_add (measure_ne_top σ _)
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  choose L hLsub hLcomp hLlt using hcpt
  set Ks : ℕ → Set X := fun n ↦ ⋃ m ∈ Finset.range (n + 1), L m with hKs
  have hKscomp : ∀ n, IsCompact (Ks n) := fun n ↦
    (Finset.range (n + 1)).isCompact_biUnion fun m _ ↦ hLcomp m
  have hKsmono : Monotone Ks := fun a b hab x hx ↦ by
    simp only [hKs, mem_iUnion, Finset.mem_range, exists_prop] at hx ⊢
    obtain ⟨m, hm, hxm⟩ := hx
    exact ⟨m, by omega, hxm⟩
  have hKscompl : ∀ n, σ (Ks n)ᶜ ≤ (n : ℝ≥0∞)⁻¹ := by
    intro n
    have hLK : L n ⊆ Ks n := fun x hx ↦ by
      simp only [hKs, mem_iUnion, Finset.mem_range, exists_prop]
      exact ⟨n, by omega, hx⟩
    refine (measure_mono (compl_subset_compl.2 hLK)).trans ?_
    rw [measure_compl (hLcomp n).isClosed.measurableSet (measure_ne_top σ _)]
    exact tsub_le_iff_left.2 (hLlt n).le
  -- Step 2: Urysohn cutoffs `φ n` equal to `1` on `Ks n`.
  choose φ hφ1 hφ0 hφsupp hφ01 using fun n ↦
    exists_continuous_one_zero_of_isCompact (hKscomp n) isClosed_empty (disjoint_empty _)
  have hφnorm : ∀ n x, ‖φ n x‖ ≤ 1 := fun n x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 n x).1]
    exact (hφ01 n x).2
  -- σ-almost every point eventually lies in `Ks n`, so the cutoffs converge to `1`.
  have hae : ∀ᵐ x ∂σ, ∀ᶠ n in atTop, φ n x = 1 := by
    have h0 : σ (⋃ n, Ks n)ᶜ = 0 := by
      rw [compl_iUnion]
      by_contra h
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
      exact absurd ((measure_mono (iInter_subset _ n)).trans (hKscompl n)) (not_le.2 hn)
    have hmem : ∀ᵐ x ∂σ, x ∈ ⋃ n, Ks n := by
      rw [ae_iff]
      exact h0
    filter_upwards [hmem] with x hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    exact eventually_atTop.2 ⟨n, fun m hm ↦ hφ1 m (hKsmono hm hn)⟩
  -- Step 3: the truncated kernels `φ n x • F x y` are continuous and compactly supported,
  -- so Mathlib's compactly supported swap applies to them.
  have hFncont : ∀ n, Continuous (uncurry fun x y ↦ φ n x • F x y) := fun n ↦
    ((φ n).continuous.comp continuous_fst).smul hF
  have hFnsupp : ∀ n, HasCompactSupport (uncurry fun x y ↦ φ n x • F x y) := by
    intro n
    apply HasCompactSupport.intro' ((hφsupp n).isCompact.prod hK.closure)
      ((isClosed_tsupport _).prod isClosed_closure)
    rintro ⟨x, y⟩ hxy
    rw [uncurry_apply_pair]
    by_cases hx : x ∈ tsupport (φ n)
    · have hy : y ∉ K := fun hyK ↦ hxy (mk_mem_prod hx (subset_closure hyK))
      rw [hsupp x y hy, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hswap : ∀ n : ℕ, ∫ x, ∫ y, φ n x • F x y ∂ν ∂σ = ∫ y, ∫ x, φ n x • F x y ∂σ ∂ν :=
    fun n ↦ integral_integral_swap_of_hasCompactSupport (hFncont n) (hFnsupp n)
  -- The partial integral in `y` is continuous and uniformly bounded.
  have hg : Continuous fun x ↦ ∫ y, F x y ∂ν :=
    continuous_integral_right_of_forall_compl_eq_zero hF hK hsupp
  have hg_bound : ∀ x, ‖∫ y, F x y ∂ν‖ ≤ C * ν.real K := fun x ↦ by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ hsupp x y hy]
    exact norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun y _ ↦ hC x y
  -- Step 4a: convergence of the left-hand sides, by dominated convergence over `σ`.
  have hLHS : Tendsto (fun n ↦ ∫ x, ∫ y, φ n x • F x y ∂ν ∂σ) atTop
      (𝓝 (∫ x, ∫ y, F x y ∂ν ∂σ)) := by
    have hmain : Tendsto (fun n ↦ ∫ x, φ n x • ∫ y, F x y ∂ν ∂σ) atTop
        (𝓝 (∫ x, ∫ y, F x y ∂ν ∂σ)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ C * ν.real K)
        (fun n ↦ (((φ n).continuous.smul hg).integrable_of_hasCompactSupport
          (hφsupp n).smul_right).aestronglyMeasurable)
        (integrable_const _) (fun n ↦ ae_of_all _ fun x ↦ ?_) ?_
      · rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n x)).trans (hg_bound x)
      · filter_upwards [hae] with x hx
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [hx] with n hn
        rw [hn, one_smul]
    refine hmain.congr fun n ↦ integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    exact (integral_smul (φ n x) (F x)).symm
  -- Step 4b: convergence of the right-hand sides, by dominated convergence over `ν`
  -- (outer) and over `σ` (inner).
  have hGncont : ∀ n, Continuous fun y ↦ ∫ x, φ n x • F x y ∂σ := fun n ↦
    continuous_integral_left_of_forall_compl_eq_zero (hFncont n) (hφsupp n).isCompact
      fun x y hx ↦ by rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have hGnsupp : ∀ n, HasCompactSupport fun y ↦ ∫ x, φ n x • F x y ∂σ := fun n ↦
    HasCompactSupport.intro' hK.closure isClosed_closure fun y hy ↦ by
      have h : ∀ x, φ n x • F x y = 0 := fun x ↦ by
        rw [hsupp x y fun hyK ↦ hy (subset_closure hyK), smul_zero]
      simp [h]
  have hRHS : Tendsto (fun n ↦ ∫ y, ∫ x, φ n x • F x y ∂σ ∂ν) atTop
      (𝓝 (∫ y, ∫ x, F x y ∂σ ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      ((closure K).indicator fun _ ↦ C * σ.real univ)
      (fun n ↦ ((hGncont n).integrable_of_hasCompactSupport
        (hGnsupp n)).aestronglyMeasurable) ?_
      (fun n ↦ ae_of_all _ fun y ↦ ?_) (ae_of_all _ fun y ↦ ?_)
    · rw [integrable_indicator_iff isClosed_closure.measurableSet]
      exact integrableOn_const hK.closure.measure_ne_top
    · by_cases hy : y ∈ closure K
      · rw [indicator_of_mem hy]
        refine norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ ?_)
        rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n x)).trans (hC x y)
      · have hy' : ∀ x, φ n x • F x y = 0 := fun x ↦ by
          rw [hsupp x y fun h ↦ hy (subset_closure h), smul_zero]
        simp [hy', indicator_of_notMem hy]
    · -- inner convergence, for every `y`, by dominated convergence over `σ`
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ C)
        (fun n ↦ (((φ n).continuous.smul (hF.uncurry_right y)).integrable_of_hasCompactSupport
          (hφsupp n).smul_right).aestronglyMeasurable)
        (integrable_const _) (fun n ↦ ae_of_all _ fun x ↦ ?_) ?_
      · rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n x)).trans (hC x y)
      · filter_upwards [hae] with x hx
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [hx] with n hn
        rw [hn, one_smul]
  -- Step 5: identify the limits.
  exact tendsto_nhds_unique hLHS (hRHS.congr fun n ↦ (hswap n).symm)

end OAI.Topology.Pontryagin.FiniteMeasureFubini.MeasureTheory
