import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.UrysohnsLemma

/-! # Density -/

namespace OAI.Topology.Pontryagin.Density.MeasureTheory

noncomputable section

open _root_.MeasureTheory

/-!
# `L¹` functions are determined by testing against `C_c`

This file fills a gap in Mathlib (general-purpose material with no project-specific content)
and is a candidate for upstreaming.

Let `X` be a locally compact Hausdorff space equipped with a regular Borel measure `μ`.
This file proves that an integrable function `u: X → ℂ` is determined, up to a.e.
equality, by the integrals `∫ x, u x * φ x ∂μ` against continuous compactly supported
test functions `φ`.

## Main results

* `exists_hasCompactSupport_integral_norm_sub_le`: continuous compactly supported functions
 are dense in `L¹(μ)`. This is a variant of
 `MeasureTheory.Integrable.exists_hasCompactSupport_integral_sub_le` that replaces the
 `NormalSpace` hypothesis (which fails for general locally compact Hausdorff spaces) by
 `T2Space` + `LocallyCompactSpace`, using the locally compact version of Urysohn's lemma.
* `norm_L1_le_of_forall_integral_le`: if `‖∫ x, u x * φ x ∂μ‖ ≤ C` for every test function
 `φ` with `‖φ‖ ≤ 1`, then `∫ x, ‖u x‖ ∂μ ≤ C`.
* `ae_eq_zero_of_forall_integral_mul_eq_zero`: if `∫ x, u x * φ x ∂μ = 0` for every test
 function `φ`, then `u = 0` a.e.

The proof of `norm_L1_le_of_forall_integral_le` is elementary: approximate `u` in `L¹` by a
continuous compactly supported `v`, then test against `φ:= conj v / max ‖v‖ δ` and let
`δ → 0`. No `L¹`–`L∞` duality is used.
-/

open Filter Set Function _root_.Topology ComplexConjugate
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.Regular]

/-- Auxiliary approximation step: on a locally compact Hausdorff space with a regular
measure, the (scaled) indicator function of a measurable set of finite measure can be
approximated in `L¹` by continuous compactly supported functions. This replaces the
`NormalSpace` Urysohn argument of `MeasureTheory.exists_continuous_eLpNorm_sub_le_of_closed`
by the locally compact Urysohn lemma. -/
theorem exists_continuous_eLpNorm_indicator_sub_le (c : ℂ) {s : Set X}
    (hs : MeasurableSet s) (hsμ : μ s < ∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ g : X → ℂ, eLpNorm (g - s.indicator fun _ => c) 1 μ ≤ δ ∧
      Continuous g ∧ HasCompactSupport g := by
  obtain ⟨δ₂, δ₂pos, hδ₂⟩ := exists_Lp_half ℂ μ 1 hδ
  obtain ⟨η, ηpos, hη⟩ := exists_eLpNorm_indicator_le ENNReal.one_ne_top c δ₂pos.ne'
  have hη' : (η : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 ηpos.ne'
  -- a compact set `k ⊆ s` catching all of `s` but a set of measure `< η`
  obtain ⟨k, hks, hk_comp, hμsk⟩ := hs.exists_isCompact_sdiff_lt hsμ.ne hη'
  have hk_meas : MeasurableSet k := hk_comp.isClosed.measurableSet
  -- an open set `U ⊇ k` exceeding `k` by a set of measure `< η`
  obtain ⟨U, hkU, hU_open, -, hμUk⟩ :=
    hk_meas.exists_isOpen_sdiff_lt ((measure_mono hks).trans_lt hsμ).ne hη'
  -- Urysohn for locally compact spaces: `f = 1` on `k`, `f = 0` outside `U`
  obtain ⟨f, hf1, hf0, hf_supp, hf_icc⟩ :=
    exists_continuous_one_zero_of_isCompact hk_comp hU_open.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hkU)
  have hg_cont : Continuous fun x => f x • c := (map_continuous f).smul continuous_const
  have hg_supp : HasCompactSupport fun x => f x • c := by
    refine hf_supp.mono fun x hx => ?_
    simp only [Function.mem_support] at hx ⊢
    intro hfx
    exact hx (by rw [hfx, zero_smul])
  refine ⟨fun x => f x • c, ?_, hg_cont, hg_supp⟩
  -- the error is supported in `(U \ k) ∪ (s \ k)`, both of measure `< η`
  have hA_meas : AEStronglyMeasurable ((fun x => f x • c) - k.indicator fun _ => c) μ :=
    hg_cont.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hk_meas)
  have hB_meas : AEStronglyMeasurable
      ((k.indicator fun _ => c) - s.indicator fun _ => c) μ :=
    (aestronglyMeasurable_const.indicator hk_meas).sub
      (aestronglyMeasurable_const.indicator hs)
  have hA : eLpNorm ((fun x => f x • c) - k.indicator fun _ => c) 1 μ
      ≤ eLpNorm ((U \ k).indicator fun _ => c) 1 μ := by
    refine eLpNorm_mono hA_meas fun x => ?_
    simp only [Pi.sub_apply]
    by_cases hxk : x ∈ k
    · simp [Set.indicator_of_mem hxk, hf1 hxk, norm_nonneg]
    · by_cases hxU : x ∈ U
      · simp only [Set.indicator_of_notMem hxk, sub_zero,
          Set.indicator_of_mem (show x ∈ U \ k from ⟨hxU, hxk⟩), norm_smul]
        refine mul_le_of_le_one_left (norm_nonneg c) ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hf_icc x).1]
        exact (hf_icc x).2
      · have hfx : f x = 0 := hf0 hxU
        simp [Set.indicator_of_notMem hxk,
          Set.indicator_of_notMem (fun h : x ∈ U \ k => hxU h.1), hfx]
  have hB : eLpNorm ((k.indicator fun _ => c) - s.indicator fun _ => c) 1 μ
      ≤ eLpNorm ((s \ k).indicator fun _ => c) 1 μ := by
    refine eLpNorm_mono hB_meas fun x => ?_
    simp only [Pi.sub_apply]
    by_cases hxk : x ∈ k
    · simp [Set.indicator_of_mem hxk, Set.indicator_of_mem (hks hxk), norm_nonneg]
    · by_cases hxs : x ∈ s
      · simp only [Set.indicator_of_notMem hxk, Set.indicator_of_mem hxs,
          Set.indicator_of_mem (show x ∈ s \ k from ⟨hxs, hxk⟩), zero_sub, norm_neg]
        exact le_rfl
      · simp [Set.indicator_of_notMem hxk, Set.indicator_of_notMem hxs,
          Set.indicator_of_notMem (fun h : x ∈ s \ k => hxs h.1)]
  have hcomb := hδ₂ _ _ (hA.trans (hη _ hμUk.le
    (hU_open.measurableSet.diff hk_meas).nullMeasurableSet))
    (hB.trans (hη _ hμsk.le (hs.diff hk_meas).nullMeasurableSet))
  rw [sub_add_sub_cancel] at hcomb
  exact hcomb.le

/-- **Density of `C_c` in `L¹`** on a locally compact Hausdorff space with a regular
measure: an integrable function can be approximated in `L¹` by continuous compactly
supported functions. Variant of
`MeasureTheory.Integrable.exists_hasCompactSupport_integral_sub_le` without the
`NormalSpace` assumption. -/
theorem exists_hasCompactSupport_integral_norm_sub_le {u : X → ℂ} (hu : Integrable u μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : X → ℂ, Continuous v ∧ HasCompactSupport v ∧ Integrable v μ ∧
      ∫ x, ‖u x - v x‖ ∂μ ≤ ε := by
  have h0P : ∀ (c : ℂ) (s : Set X), MeasurableSet s → μ s < ∞ → ∀ (δ : ℝ≥0∞), δ ≠ 0 →
      ∃ g : X → ℂ, eLpNorm (g - s.indicator fun _ => c) 1 μ ≤ δ ∧
        Continuous g ∧ HasCompactSupport g :=
    fun c s hs hsμ δ hδ => exists_continuous_eLpNorm_indicator_sub_le c hs hsμ hδ
  have h1P : ∀ f g : X → ℂ, Continuous f ∧ HasCompactSupport f →
      Continuous g ∧ HasCompactSupport g →
      Continuous (f + g) ∧ HasCompactSupport (f + g) :=
    fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  have hu1 : MemLp u 1 μ := memLp_one_iff_integrable.2 hu
  obtain ⟨v, hv_norm, hv_cont, hv_supp⟩ :=
    hu1.induction_dense ENNReal.one_ne_top
      (fun g => Continuous g ∧ HasCompactSupport g) h0P h1P
      (ENNReal.ofReal_pos.2 hε).ne'
  have hv_int : Integrable v μ := hv_cont.integrable_of_hasCompactSupport hv_supp
  refine ⟨v, hv_cont, hv_supp, hv_int, ?_⟩
  have hsub : Integrable (fun x => u x - v x) μ := hu.sub' hv_int
  rw [integral_norm_eq_lintegral_enorm hsub.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hε.le ?_
  have heq : eLpNorm (u - v) 1 μ = ∫⁻ x, ‖u x - v x‖ₑ ∂μ := by
    exact eLpNorm_one_eq_lintegral_enorm hsub.aestronglyMeasurable
  rw [← heq]
  exact hv_norm

/-- If an integrable function `u` satisfies `‖∫ x, u x * φ x ∂μ‖ ≤ C` for every continuous
compactly supported `φ` with `‖φ‖ ≤ 1`, then `∫ x, ‖u x‖ ∂μ ≤ C`.

The nonnegativity hypothesis follows from `h` applied to `φ = 0`, but is included
for convenience of callers. -/
theorem norm_L1_le_of_forall_integral_le {u : X → ℂ} (hu : Integrable u μ) {C : ℝ}
    (_hC : 0 ≤ C)
    (h : ∀ φ : X → ℂ, Continuous φ → HasCompactSupport φ → (∀ x, ‖φ x‖ ≤ 1) →
      ‖∫ x, u x * φ x ∂μ‖ ≤ C) :
    ∫ x, ‖u x‖ ∂μ ≤ C := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨v, hv_cont, hv_supp, hv_int, hv_close⟩ :=
    exists_hasCompactSupport_integral_norm_sub_le hu (half_pos hε)
  have hts_meas : MeasurableSet (tsupport v) := (isClosed_tsupport v).measurableSet
  have hind_int : Integrable ((tsupport v).indicator fun _ => (1 : ℝ)) μ :=
    (integrable_indicator_iff hts_meas).2
      (integrableOn_const (IsCompact.measure_lt_top hv_supp).ne)
  have hind_eq : ∫ x, (tsupport v).indicator (fun _ => (1 : ℝ)) x ∂μ
      = μ.real (tsupport v) := by
    rw [integral_indicator_const (1 : ℝ) hts_meas, smul_eq_mul, mul_one]
  -- key estimate: the `L¹`-norm of the approximant `v` is at most `ε / 2 + C`
  have key : ∫ x, ‖v x‖ ∂μ ≤ ε / 2 + C := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hM0 : (0 : ℝ) ≤ μ.real (tsupport v) := measureReal_nonneg
    have hM1 : (0 : ℝ) < μ.real (tsupport v) + 1 := by linarith
    set δ : ℝ := η / (μ.real (tsupport v) + 1) with hδdef
    have hδ_pos : 0 < δ := div_pos hη hM1
    have hδM : δ * μ.real (tsupport v) ≤ η := by
      rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hM1]
      exact mul_le_mul_of_nonneg_left (by linarith) hη.le
    -- the test function `φ = conj v / max ‖v‖ δ`
    set φ : X → ℂ := fun y => conj (v y) / Complex.ofReal (max ‖v y‖ δ) with hφdef
    have hmax_pos : ∀ y : X, (0 : ℝ) < max ‖v y‖ δ := fun y => lt_max_of_lt_right hδ_pos
    have hφ_cont : Continuous φ := by
      rw [hφdef]
      refine Continuous.div (Complex.continuous_conj.comp hv_cont)
        (Complex.continuous_ofReal.comp (hv_cont.norm.max continuous_const)) fun y => ?_
      exact Complex.ofReal_ne_zero.mpr (hmax_pos y).ne'
    have hφ_bd : ∀ y, ‖φ y‖ ≤ 1 := by
      intro y
      simp only [hφdef]
      rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hmax_pos y)]
      exact div_le_one_of_le₀ (le_max_left _ _) (hmax_pos y).le
    have hφ_supp : HasCompactSupport φ := by
      refine hv_supp.mono fun y hy => ?_
      simp only [Function.mem_support] at hy ⊢
      intro hvy
      refine hy ?_
      simp only [hφdef]
      rw [hvy, map_zero, zero_div]
    have hφ_val : ∀ y, v y * φ y = Complex.ofReal (‖v y‖ ^ 2 / max ‖v y‖ δ) := by
      intro y
      simp only [hφdef]
      rw [Complex.ofReal_div, Complex.ofReal_pow, ← Complex.mul_conj']
      ring
    have hφ_meas : AEStronglyMeasurable φ μ := hφ_cont.aestronglyMeasurable
    have hvφ_int : Integrable (fun y => v y * φ y) μ :=
      hv_int.mul_bdd hφ_meas (Eventually.of_forall hφ_bd)
    have huφ_int : Integrable (fun y => u y * φ y) μ :=
      hu.mul_bdd hφ_meas (Eventually.of_forall hφ_bd)
    have hsub_int : Integrable (fun y => (v y - u y) * φ y) μ :=
      (hv_int.sub' hu).mul_bdd hφ_meas (Eventually.of_forall hφ_bd)
    have h1 : Integrable (fun y => (v y * φ y).re) μ := hvφ_int.re
    have h2 : Integrable
        (fun y => δ * (tsupport v).indicator (fun _ => (1 : ℝ)) y) μ :=
      hind_int.const_mul δ
    -- pointwise: `‖v‖ ≤ Re (v * φ) + δ · 1_{tsupport v}`
    have hpoint : ∀ y, ‖v y‖ ≤ (v y * φ y).re
        + δ * (tsupport v).indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ tsupport v
      · simp only [Set.indicator_of_mem hy, mul_one, hφ_val y, Complex.ofReal_re]
        rcases le_or_gt δ ‖v y‖ with hcase | hcase
        · have hne : ‖v y‖ ≠ 0 := (hδ_pos.trans_le hcase).ne'
          rw [max_eq_left hcase, sq, mul_div_assoc, div_self hne, mul_one]
          linarith
        · have hq : (0 : ℝ) ≤ ‖v y‖ ^ 2 / max ‖v y‖ δ := by positivity
          linarith
      · simp [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy]
    have hre_int : ∫ y, (v y * φ y).re ∂μ = (∫ y, v y * φ y ∂μ).re := by
      simp_rw [← RCLike.re_to_complex]
      exact integral_re hvφ_int
    -- `‖∫ v φ‖ ≤ ε / 2 + C` by comparison with `u`
    have hsplit : ∫ y, v y * φ y ∂μ
        = ∫ y, (v y - u y) * φ y ∂μ + ∫ y, u y * φ y ∂μ := by
      rw [← integral_add hsub_int huφ_int]
      exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    have hvφ_le : ‖∫ y, v y * φ y ∂μ‖ ≤ ε / 2 + C := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ (h φ hφ_cont hφ_supp hφ_bd))
      calc ‖∫ y, (v y - u y) * φ y ∂μ‖ ≤ ∫ y, ‖u y - v y‖ ∂μ := by
            refine norm_integral_le_of_norm_le (hu.sub' hv_int).norm
              (Eventually.of_forall fun y => ?_)
            rw [norm_mul, norm_sub_rev]
            exact mul_le_of_le_one_right (norm_nonneg _) (hφ_bd y)
        _ ≤ ε / 2 := hv_close
    calc ∫ y, ‖v y‖ ∂μ
        ≤ ∫ y, ((v y * φ y).re
            + δ * (tsupport v).indicator (fun _ => (1 : ℝ)) y) ∂μ :=
          integral_mono hv_int.norm (h1.add h2) hpoint
      _ = ∫ y, (v y * φ y).re ∂μ
            + ∫ y, δ * (tsupport v).indicator (fun _ => (1 : ℝ)) y ∂μ :=
          integral_add h1 h2
      _ = (∫ y, v y * φ y ∂μ).re + δ * μ.real (tsupport v) := by
          rw [hre_int, integral_const_mul, hind_eq]
      _ ≤ ‖∫ y, v y * φ y ∂μ‖ + δ * μ.real (tsupport v) :=
          add_le_add (RCLike.re_le_norm (∫ y, v y * φ y ∂μ)) le_rfl
      _ ≤ (ε / 2 + C) + δ * μ.real (tsupport v) := add_le_add hvφ_le le_rfl
      _ ≤ ε / 2 + C + η := by linarith
  calc ∫ x, ‖u x‖ ∂μ
      ≤ ∫ x, (‖u x - v x‖ + ‖v x‖) ∂μ :=
        integral_mono hu.norm ((hu.sub' hv_int).norm.add hv_int.norm) fun x => by
          calc ‖u x‖ = ‖u x - v x + v x‖ := by rw [sub_add_cancel]
            _ ≤ ‖u x - v x‖ + ‖v x‖ := norm_add_le _ _
    _ = ∫ x, ‖u x - v x‖ ∂μ + ∫ x, ‖v x‖ ∂μ :=
        integral_add (hu.sub' hv_int).norm hv_int.norm
    _ ≤ ε / 2 + (ε / 2 + C) := add_le_add hv_close key
    _ = C + ε := by ring

/-- **`L¹` functions are determined by testing against `C_c`**: if an integrable function
`u` satisfies `∫ x, u x * φ x ∂μ = 0` for every continuous compactly supported `φ`, then
`u = 0` almost everywhere. -/
theorem ae_eq_zero_of_forall_integral_mul_eq_zero {u : X → ℂ} (hu : Integrable u μ)
    (h : ∀ φ : X → ℂ, Continuous φ → HasCompactSupport φ → ∫ x, u x * φ x ∂μ = 0) :
    u =ᵐ[μ] 0 := by
  have h0 : ∫ x, ‖u x‖ ∂μ ≤ 0 :=
    norm_L1_le_of_forall_integral_le hu le_rfl fun φ hφc hφs _ => by
      simp [h φ hφc hφs]
  have h1 : (fun x => ‖u x‖) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (u x)) hu.norm).1
      (le_antisymm h0 (integral_nonneg fun x => norm_nonneg _))
  filter_upwards [h1] with x hx
  simpa using hx

end

end OAI.Topology.Pontryagin.Density.MeasureTheory
