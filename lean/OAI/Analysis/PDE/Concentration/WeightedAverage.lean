import OAI.Analysis.PDE.Concentration.MeanIdentity

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Filter Metric InnerProductSpace
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

noncomputable def weightedBallAverage (f : E → ℝ) (x : E) (r : ℝ) : ℝ :=
  ∫ y, meanWeight y * f (x + r • y)

theorem hasDerivAt_weightedBallAverage {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) (r : ℝ) :
    HasDerivAt (weightedBallAverage f x)
      (∫ y, meanWeight y * fderiv ℝ f (x + r • y) y) r := by
  have hdf := (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).continuous
  have hc : Continuous (fun p : ℝ × E => meanWeight p.2 * fderiv ℝ f (x + p.1 • p.2) p.2) :=
    (contDiff_meanWeight.continuous.comp continuous_snd).mul
      ((hdf.comp (continuous_const.add (continuous_fst.smul continuous_snd))).clm_apply continuous_snd)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall r 1).prod
    (isCompact_closedBall (0 : E) 1)).exists_bound_of_continuousOn hc.continuousOn
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  let β : ContDiffBump (0 : E) :=
    {rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num}
  have hb : Integrable (fun y : E => D * β y) :=
    (continuous_const.mul β.continuous).integrable_of_hasCompactSupport β.hasCompactSupport.mul_left
  have hd (s : ℝ) (y : E) : HasDerivAt (fun t : ℝ => meanWeight y * f (x + t • y))
      (meanWeight y * fderiv ℝ f (x + s • y) y) s := by
    have hg : HasDerivAt (fun t : ℝ => x + t • y) y s :=
      by simpa using ((hasDerivAt_id s).smul_const y).const_add x
    exact ((hf.differentiable (by norm_num) (x + s • y)).hasFDerivAt.comp_hasDerivAt s hg).const_mul
      (meanWeight y)
  have hF (s : ℝ) : Continuous (fun y : E => meanWeight y * f (x + s • y)) :=
    contDiff_meanWeight.continuous.mul (hf.continuous.comp (continuous_const.add (continuous_id.const_smul s)))
  have hcont' : Continuous (fun y : E => meanWeight y * fderiv ℝ f (x + r • y) y) :=
    hc.comp (continuous_const.prodMk continuous_id)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure E)) (F := fun s y => meanWeight y * f (x + s • y))
    (F' := fun s y => meanWeight y * fderiv ℝ f (x + s • y) y)
    (closedBall_mem_nhds r (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun s => (hF s).aestronglyMeasurable))
    ((hF r).integrable_of_hasCompactSupport hasCompactSupport_meanWeight.mul_right)
    hcont'.aestronglyMeasurable (bound := fun y => D * β y) ?_ hb
    (Filter.Eventually.of_forall (fun y s _ => hd s y))
  · exact h.2
  · apply Filter.Eventually.of_forall
    intro y s hs
    by_cases hy : y ∈ closedBall (0 : E) 1
    · have he : β y = 1 := β.one_of_mem_closedBall hy
      rw [he, mul_one]
      exact (hC (s, y) ⟨hs, hy⟩).trans (le_max_left _ _)
    · have hw : meanWeight y = 0 := by
        apply meanWeight_zero
        simpa only [mem_closedBall, dist_zero_right, not_le] using hy
      rw [hw, zero_mul, norm_zero]
      exact mul_nonneg hD β.nonneg

end OAI.Analysis.PDE.Concentration
