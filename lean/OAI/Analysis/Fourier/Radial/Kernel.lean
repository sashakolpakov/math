import OAI.Analysis.Fourier.SquareFunction.EuclideanMaximal

/-! Domination of radial decreasing kernels by the actual ball maximal function.
Writing a radial kernel as an integral of balls makes the domination a Tonelli
identity followed by the definition of the maximal function. -/

namespace OAI.Analysis.Fourier.Radial

open _root_.MeasureTheory Set Metric
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- The integral of a nonnegative function over a ball is controlled by its
uncentered maximal function at the center. -/
theorem ball_integral_le_maximal_mul_measure (μ : Measure X) (f : X → ℝ≥0∞)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (x : X) (r : ℝ) :
    (∫⁻ y in ball x r, f y ∂μ) ≤ OAI.Analysis.Fourier.SquareFunction.ballMaximal μ f x * μ (ball x r) := by
  by_cases hr : 0 < r
  · have h : OAI.Analysis.Fourier.SquareFunction.ballAverage μ f (x, r) ≤ OAI.Analysis.Fourier.SquareFunction.ballMaximal μ f x :=
      le_iSup_of_le (x, r) (le_iSup_of_le (mem_ball_self hr) le_rfl)
    exact (ENNReal.div_le_iff_le_mul (.inl (hball x r hr).1) (.inl (hball x r hr).2)).mp h
  · simp [ball_eq_empty.mpr (le_of_not_gt hr)]

/-- Exact Tonelli formula expressing a radial tail kernel as weighted ball integrals. -/
theorem integral_radial_tail_eq_ball_integrals
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k) (x : X) :
    (∫⁻ y, f y * (∫⁻ r in Ioi (dist y x), k r) ∂μ) =
      ∫⁻ r : ℝ, k r * (∫⁻ y in ball x r, f y ∂μ) := by
  let F : X × ℝ → ℝ≥0∞ := {z | dist z.1 x < z.2}.indicator (fun z => f z.1 * k z.2)
  have hF : Measurable F := ((hf.comp measurable_fst).mul (hk.comp measurable_snd)).indicator
    (measurableSet_lt ((continuous_id.dist continuous_const).measurable.comp measurable_fst)
      measurable_snd)
  have hleft (y : X) : (∫⁻ r : ℝ, F (y, r)) = f y * ∫⁻ r in Ioi (dist y x), k r := by
    change (∫⁻ r : ℝ, (Ioi (dist y x)).indicator (fun r => f y * k r) r) = _
    rw [lintegral_indicator measurableSet_Ioi, lintegral_const_mul _ hk]
  have hright (r : ℝ) : (∫⁻ y, F (y, r) ∂μ) = k r * ∫⁻ y in ball x r, f y ∂μ := by
    change (∫⁻ y, (ball x r).indicator (fun y => f y * k r) y ∂μ) = _
    rw [lintegral_indicator isOpen_ball.measurableSet, lintegral_mul_const _ hf, mul_comm]
  calc
    _ = ∫⁻ y, (∫⁻ r : ℝ, F (y, r)) ∂μ := by simp_rw [hleft]
    _ = ∫⁻ r : ℝ, ∫⁻ y, F (y, r) ∂μ :=
      lintegral_lintegral_swap (μ := μ) (ν := volume) (f := fun y r => F (y, r)) hF.aemeasurable
    _ = _ := by simp_rw [hright]

/-- A radial kernel assembled from nonnegative ball weights is dominated by
the maximal function times the kernel's mass. -/
theorem integral_radial_tail_le_maximal
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞) (x : X) :
    (∫⁻ y, f y * (∫⁻ r in Ioi (dist y x), k r) ∂μ) ≤
      OAI.Analysis.Fourier.SquareFunction.ballMaximal μ f x * ∫⁻ r : ℝ, k r * μ (ball x r) := by
  rw [integral_radial_tail_eq_ball_integrals μ hf hk x]
  have hm : Measurable (fun r : ℝ => μ (ball x r)) :=
    (show Monotone (fun r : ℝ => μ (ball x r)) from
      fun r s hrs => measure_mono (ball_subset_ball hrs)).measurable
  calc
    _ ≤ ∫⁻ r : ℝ, k r * (OAI.Analysis.Fourier.SquareFunction.ballMaximal μ f x * μ (ball x r)) := by
      apply lintegral_mono
      intro r
      exact mul_le_mul_right (ball_integral_le_maximal_mul_measure μ f hball x r) _
    _ = ∫⁻ r : ℝ, OAI.Analysis.Fourier.SquareFunction.ballMaximal μ f x * (k r * μ (ball x r)) := by
      apply lintegral_congr
      intro r
      ac_rfl
    _ = _ := lintegral_const_mul _ (hk.mul hm)

/-- The maximal domination in terms of the actual mass of the radial kernel. -/
theorem integral_radial_tail_le_maximal_mul_mass
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞) (x : X) :
    (∫⁻ y, f y * (∫⁻ r in Ioi (dist y x), k r) ∂μ) ≤
      OAI.Analysis.Fourier.SquareFunction.ballMaximal μ f x * ∫⁻ y, (∫⁻ r in Ioi (dist y x), k r) ∂μ := by
  have he := integral_radial_tail_eq_ball_integrals μ (f := fun _ => 1) measurable_const hk x
  simp only [one_mul, setLIntegral_one] at he
  rw [he]
  exact integral_radial_tail_le_maximal μ hf hk hball x

/-- The polynomial kernels in the combining-dilates argument are radial tails. -/
theorem polynomial_radial_tail {q d : ℝ} (hq : 0 < q) (hd : 0 ≤ d) :
    (∫⁻ r in Ioi d, ENNReal.ofReal (q * (r + 1) ^ (-q - 1))) =
      ENNReal.ofReal ((d + 1) ^ (-q)) := by
  have hi : IntegrableOn (fun r : ℝ => q * (r + 1) ^ (-q - 1)) (Ioi d) :=
    (integrableOn_add_rpow_Ioi_of_lt (by linarith : -q - 1 < -1)
      (by linarith : -(1 : ℝ) < d)).const_mul q
  have hn : ∀ᵐ r : ℝ ∂volume.restrict (Ioi d), 0 ≤ q * (r + 1) ^ (-q - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : d < r := hr
    exact mul_nonneg hq.le (Real.rpow_nonneg (by linarith : 0 ≤ r + 1) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have hder : ∀ r ∈ Ici d, HasDerivAt (fun t : ℝ => -(t + 1) ^ (-q))
      (q * (r + 1) ^ (-q - 1)) r := by
    intro r hr
    have hr' : d ≤ r := hr
    convert! (((hasDerivAt_id r).add_const 1).rpow_const
      (p := -q) (Or.inl (by linarith : r + 1 ≠ 0))).neg using 1 ;
      simp only [id_eq] ; ring
  have ht : Filter.Tendsto (fun t : ℝ => -(t + 1) ^ (-q)) Filter.atTop (nhds 0) := by
    simpa only [neg_zero, Function.comp_def, id_eq] using ((tendsto_rpow_neg_atTop hq).comp
      (Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id)).neg
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hder hi ht
  simpa only [zero_sub, neg_neg] using congrArg ENNReal.ofReal he

/-- Actual polynomial radial kernels are bounded by their mass times `Mf`. -/
theorem integral_polynomial_kernel_le_maximal
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    {q : ℝ} (hq : 0 < q) (x : X) :
    (∫⁻ y, f y * ENNReal.ofReal ((dist y x + 1) ^ (-q)) ∂μ) ≤
      OAI.Analysis.Fourier.SquareFunction.ballMaximal μ f x * ∫⁻ y, ENNReal.ofReal ((dist y x + 1) ^ (-q)) ∂μ := by
  have hk : Measurable (fun r : ℝ => ENNReal.ofReal (q * (r + 1) ^ (-q - 1))) :=
    (measurable_const.mul ((measurable_id.add_const 1).pow_const _)).ennreal_ofReal
  have h := integral_radial_tail_le_maximal_mul_mass μ hf hk hball x
  simpa only [polynomial_radial_tail hq dist_nonneg] using h

theorem polynomial_radial_tail_scaled {q d a : ℝ}
    (hq : 0 < q) (hd : 0 ≤ d) (ha : 0 < a) :
    (∫⁻ r in Ioi d, ENNReal.ofReal (a * q * (a * r + 1) ^ (-q - 1))) =
      ENNReal.ofReal ((a * d + 1) ^ (-q)) := by
  have hder : ∀ r ∈ Ici d, HasDerivAt (fun t : ℝ => -(a * t + 1) ^ (-q))
      (a * q * (a * r + 1) ^ (-q - 1)) r := by
    intro r hr
    have hr' : d ≤ r := hr
    have hbase : a * r + 1 ≠ 0 := ne_of_gt (by nlinarith : 0 < a * r + 1)
    convert! (((hasDerivAt_id r).const_mul a |>.add_const 1).rpow_const
      (p := -q) (Or.inl hbase)).neg using 1 ; simp only [id_eq] ; ring
  have ht : Filter.Tendsto (fun t : ℝ => -(a * t + 1) ^ (-q)) Filter.atTop (nhds 0) := by
    simpa only [neg_zero, Function.comp_def, id_eq] using ((tendsto_rpow_neg_atTop hq).comp
      (Filter.tendsto_atTop_add_const_right _ 1 (Filter.Tendsto.const_mul_atTop ha Filter.tendsto_id))).neg
  have hn : ∀ r ∈ Ioi d, 0 ≤ a * q * (a * r + 1) ^ (-q - 1) := by
    intro r hr
    have hr' : d < r := hr
    exact mul_nonneg (mul_nonneg ha.le hq.le) (Real.rpow_nonneg (by nlinarith) _)
  have hi := integrableOn_Ioi_deriv_of_nonneg' hder hn ht
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hn r hr)]
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hder hi ht
  simpa only [zero_sub, neg_neg] using congrArg ENNReal.ofReal he

theorem integral_scaled_polynomial_kernel_le_maximal
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f)
    (hball : ∀ x r, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    {q a : ℝ} (hq : 0 < q) (ha : 0 < a) (x : X) :
    (∫⁻ y, f y * ENNReal.ofReal ((a * dist y x + 1) ^ (-q)) ∂μ) ≤
      OAI.Analysis.Fourier.SquareFunction.ballMaximal μ f x * ∫⁻ y, ENNReal.ofReal ((a * dist y x + 1) ^ (-q)) ∂μ := by
  have hk : Measurable (fun r : ℝ => ENNReal.ofReal (a * q * (a * r + 1) ^ (-q - 1))) :=
    (measurable_const.mul (((measurable_const.mul measurable_id).add_const 1).pow_const _)).ennreal_ofReal
  have h := integral_radial_tail_le_maximal_mul_mass μ hf hk hball x
  simpa only [polynomial_radial_tail_scaled hq dist_nonneg ha] using h

end OAI.Analysis.Fourier.Radial
