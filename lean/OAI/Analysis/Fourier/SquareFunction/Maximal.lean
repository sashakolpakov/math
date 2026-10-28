import Mathlib

/-!
The strong-type step in the maximal-function argument in `stein_square.tex`.
The estimates below are for actual superlevel sets and Lebesgue integrals.
-/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set intervalIntegral
open scoped ENNReal

private theorem primitive_power {p : ℝ} (hp : 0 < p) (b : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..b, p * t ^ (p - 1)) = b ^ p := by
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < p - 1))]
  simp only [sub_add_cancel, Real.zero_rpow (ne_of_gt hp), sub_zero]
  field_simp

/-- The `p`th moment is the weighted integral of the superlevel-set measures. -/
theorem lintegral_power_layercake {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x} *
        ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hfn) hf.aemeasurable
    (g := fun t : ℝ => p * t ^ (p - 1))
    (fun t ht => (intervalIntegrable_rpow' (by linarith : -1 < p - 1)).const_mul p)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg hp.le (Real.rpow_nonneg ht.le _))
  simp_rw [primitive_power hp] at h
  calc
    _ = ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ := by
      apply lintegral_congr; intro x
      exact ENNReal.ofReal_rpow_of_nonneg (hfn x) hp.le
    _ = _ := h.trans (lintegral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_rpow_of_pos ht]
      exact (mul_assoc _ _ _).symm))

/-- A finite power integral in the form used after interchanging tail integrals. -/
theorem lintegral_power_Ioo {b q : ℝ} (hb : 0 ≤ b) (hq : -1 < q) :
    (∫⁻ t : ℝ in Ioo 0 b, ENNReal.ofReal t ^ q) =
      ENNReal.ofReal (b ^ (q + 1) / (q + 1)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ q) (Ioo 0 b) :=
    (intervalIntegrable_rpow' hq (a := 0) (b := b)).1.mono_set Ioo_subset_Ioc_self
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 b), 0 ≤ t ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  calc
    _ = ∫⁻ t : ℝ in Ioo 0 b, ENNReal.ofReal (t ^ q) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ENNReal.ofReal_rpow_of_pos ht.1
    _ = ENNReal.ofReal (∫ t : ℝ in Ioo 0 b, t ^ q) := (ofReal_integral_eq_lintegral_ofReal hi hn).symm
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb,
        integral_rpow (Or.inl hq)]
      simp [Real.zero_rpow (by linarith : q + 1 ≠ 0)]

/-- Tonelli evaluation of the weighted integral of truncated first moments. -/
theorem lintegral_weighted_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {q : ℝ} (hq : -1 < q) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) * ENNReal.ofReal t ^ q) =
      ENNReal.ofReal (1 / (q + 1)) * ∫⁻ x, ENNReal.ofReal (f x) ^ (q + 2) ∂μ := by
  let F : X × ℝ → ℝ≥0∞ := {z | z.2 < f z.1}.indicator
    (fun z => ENNReal.ofReal (f z.1) * ENNReal.ofReal z.2 ^ q)
  have hF : Measurable F :=
    ((hf.comp measurable_fst).ennreal_ofReal.mul
      (measurable_snd.ennreal_ofReal.pow_const q)).indicator
      (measurableSet_lt measurable_snd (hf.comp measurable_fst))
  have hleft (t : ℝ) : (∫⁻ x, F (x, t) ∂μ) =
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) * ENNReal.ofReal t ^ q := by
    change (∫⁻ x, {x | t < f x}.indicator
      (fun x => ENNReal.ofReal (f x) * ENNReal.ofReal t ^ q) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_lt measurable_const hf),
      lintegral_mul_const _ hf.ennreal_ofReal]
  have hright (x : X) : (∫⁻ t in Ioi (0 : ℝ), F (x, t)) =
      ENNReal.ofReal (1 / (q + 1)) * ENNReal.ofReal (f x) ^ (q + 2) := by
    change (∫⁻ t in Ioi (0 : ℝ), (Iio (f x)).indicator
      (fun t => ENNReal.ofReal (f x) * ENNReal.ofReal t ^ q) t) = _
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      inter_comm (Iio (f x)), Ioi_inter_Iio,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_power_Ioo (hfn x) hq]
    have hq1 : 0 < q + 1 := by linarith
    have hq2 : 0 ≤ q + 2 := by linarith
    rw [ENNReal.ofReal_div_of_pos hq1, ← ENNReal.ofReal_rpow_of_nonneg (hfn x) hq1.le,
      ENNReal.ofReal_div_of_pos hq1, ENNReal.ofReal_one]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have he : ENNReal.ofReal (f x) ^ (q + 2) =
        ENNReal.ofReal (f x) ^ (q + 1) * ENNReal.ofReal (f x) := by
      simpa only [show q + 1 + 1 = q + 2 by ring, ENNReal.rpow_one] using
        (ENNReal.rpow_add_of_nonneg (x := ENNReal.ofReal (f x))
          (q + 1) 1 hq1.le zero_le_one)
    rw [he, one_mul]
    ac_rfl
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F (x, t) ∂μ := by simp_rw [hleft]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), F (x, t)) ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ)))
        (f := fun x t => F (x, t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hright]
      exact lintegral_const_mul _ (hf.ennreal_ofReal.pow_const _)

/-- The strong-type conclusion from the truncated weak estimate.  This is the
layer-cake step for the Hardy--Littlewood maximal operator; the geometric
covering argument is deliberately not included among this lemma's conclusions. -/
theorem power_moment_le_of_truncated_weak_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {u f : X → ℝ} (hu : Measurable u) (hf : Measurable f)
    (hun : ∀ x, 0 ≤ u x) (hfn : ∀ x, 0 ≤ f x)
    {p C : ℝ} (hp : 1 < p) (hC : 0 ≤ C)
    (hweak : ∀ t > 0, μ {x | t < u x} ≤
      ENNReal.ofReal C / ENNReal.ofReal t *
        ∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (u x) ^ p ∂μ) ≤
      ENNReal.ofReal (C * p / (p - 1)) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), μ {x | t < u x} *
        ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) :=
      lintegral_power_layercake μ hu hun hp0
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (ENNReal.ofReal C * ENNReal.ofReal p) *
        ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) *
          ENNReal.ofReal t ^ (p - 2)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have he : ENNReal.ofReal t ^ (p - 2) =
          ENNReal.ofReal t ^ (p - 1) / ENNReal.ofReal t := by
        simpa only [show p - 1 - 1 = p - 2 by ring, ENNReal.rpow_one] using
          ENNReal.rpow_sub (x := ENNReal.ofReal t) (p - 1) 1
            (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top
      calc
        _ ≤ (ENNReal.ofReal C / ENNReal.ofReal t *
              ∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ∂μ) *
              ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) :=
          by gcongr; exact hweak t ht
        _ = _ := by rw [he]; simp only [div_eq_mul_inv]; ac_rfl
    _ = (ENNReal.ofReal C * ENNReal.ofReal p) *
        (ENNReal.ofReal (1 / (p - 1)) *
          ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ) := by
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
        lintegral_weighted_tail μ hf hfn (by linarith : -1 < p - 2)]
      simp only [show p - 2 + 1 = p - 1 by ring, show p - 2 + 2 = p by ring]
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hC,
        ← ENNReal.ofReal_mul (mul_nonneg hC hp0.le)]
      congr 2
      ring

/-- The geometric weak-type estimate.  Vitali's disjoint subfamily controls the
union of any bounded-radius family of balls by their integral averages. -/
theorem measure_ball_union_le_of_integral
    {X I : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (s : Set I) (c : I → X) (r : I → ℝ)
    (R : ℝ) (hr0 : ∀ i ∈ s, 0 < r i) (hrR : ∀ i ∈ s, r i ≤ R)
    {D a : ℝ≥0∞}
    (hdbl : ∀ i ∈ s, μ (Metric.ball (c i) (5 * r i)) ≤ D * μ (Metric.ball (c i) (r i)))
    (havg : ∀ i ∈ s, μ (Metric.ball (c i) (r i)) ≤
      a * ∫⁻ x in Metric.ball (c i) (r i), f x ∂μ) :
    μ (⋃ i ∈ s, Metric.ball (c i) (r i)) ≤ D * a * ∫⁻ x, f x ∂μ := by
  obtain ⟨u, hus, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      s c r R hrR 5 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen
    (fun i hi => Metric.isOpen_ball)
    (fun i hi => ⟨c i, Metric.mem_ball_self (hr0 i (hus hi))⟩)
  let : Countable u := huc.to_subtype
  have hsub : (⋃ i ∈ s, Metric.ball (c i) (r i)) ⊆
      ⋃ i : u, Metric.ball (c i) (5 * r i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hxi⟩
  calc
    _ ≤ μ (⋃ i : u, Metric.ball (c i) (5 * r i)) := measure_mono hsub
    _ ≤ ∑' i : u, μ (Metric.ball (c i) (5 * r i)) := measure_iUnion_le _
    _ ≤ ∑' i : u, D * (a * ∫⁻ x in Metric.ball (c i) (r i), f x ∂μ) := by
      apply ENNReal.tsum_le_tsum
      intro i
      apply (hdbl i (hus i.property)).trans
      gcongr
      exact havg i (hus i.property)
    _ = D * a * (∑' i : u, ∫⁻ x in Metric.ball (c i) (r i), f x ∂μ) := by
      simp_rw [← mul_assoc]
      exact ENNReal.tsum_mul_left
    _ = D * a * ∫⁻ x in ⋃ i : u, Metric.ball (c i) (r i), f x ∂μ := by
      rw [lintegral_iUnion (fun i => Metric.isOpen_ball.measurableSet) (hdisj.subtype _ _) f]
    _ ≤ _ := by gcongr; exact Measure.restrict_le_self

/-- Removing the radius bound by continuity of measure from below. -/
theorem measure_ball_union_le_of_integral_unbounded
    {X I : Type*} [PseudoMetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (s : Set I) (c : I → X) (r : I → ℝ)
    (hr0 : ∀ i ∈ s, 0 < r i) {D a : ℝ≥0∞}
    (hdbl : ∀ i ∈ s, μ (Metric.ball (c i) (5 * r i)) ≤ D * μ (Metric.ball (c i) (r i)))
    (havg : ∀ i ∈ s, μ (Metric.ball (c i) (r i)) ≤
      a * ∫⁻ x in Metric.ball (c i) (r i), f x ∂μ) :
    μ (⋃ i ∈ s, Metric.ball (c i) (r i)) ≤ D * a * ∫⁻ x, f x ∂μ := by
  let U : ℕ → Set X := fun N => ⋃ i ∈ {i ∈ s | r i ≤ (N : ℝ)}, Metric.ball (c i) (r i)
  have hmono : Monotone U := by
    intro N M hNM
    apply iUnion₂_mono'
    intro i hi
    exact ⟨i, ⟨hi.1, hi.2.trans (by exact_mod_cast hNM)⟩, Subset.rfl⟩
  have hU : (⋃ i ∈ s, Metric.ball (c i) (r i)) = ⋃ N, U N := by
    ext x
    simp only [U, mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, hxi⟩
      obtain ⟨N, hN⟩ := exists_nat_ge (r i)
      exact ⟨N, i, ⟨hi, hN⟩, hxi⟩
    · rintro ⟨N, i, ⟨hi, hN⟩, hxi⟩
      exact ⟨i, hi, hxi⟩
  rw [hU, hmono.measure_iUnion]
  apply iSup_le
  intro N
  exact measure_ball_union_le_of_integral μ f {i ∈ s | r i ≤ (N : ℝ)} c r N
    (fun i hi => hr0 i hi.1) (fun i hi => hi.2)
    (fun i hi => hdbl i hi.1) (fun i hi => havg i hi.1)

end OAI.Analysis.Fourier.SquareFunction
