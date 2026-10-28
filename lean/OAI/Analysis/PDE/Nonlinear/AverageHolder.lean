import OAI.Analysis.PDE.Nonlinear.Average

/-! Segment-averaged smooth coefficients act on bounded Hölder fields uniformly. -/

noncomputable section
open Set Metric _root_.MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder

theorem exists_segmentAverage_holder_bound {X E F : Type*}
    [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (hg : ContDiff ℝ 1 g) {α R : ℝ} (hα : 0 < α) (_ : 0 ≤ R) :
    ∃ C ≥ 0, ∀ A B : OAI.Analysis.Normed.Function.Holder.HolderMap X E α, ‖A‖ ≤ R → ‖B‖ ≤ R →
      ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap X F α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = segmentAverage g (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x)) ∧
        ‖H‖ ≤ C * (1 + ‖A‖ + ‖B‖) := by
  obtain ⟨L, hLip⟩ := hg.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hg.continuous.continuousOn
  let C : ℝ := |M| + L + 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hMC : M ≤ C := by dsimp only [C]; linarith [le_abs_self M, L.coe_nonneg]
  have hLC : (L : ℝ) ≤ C := by dsimp only [C]; linarith [abs_nonneg M]
  have hgM (x : E) (hx : ‖x‖ ≤ R) : ‖g x‖ ≤ M :=
    hM x (by simpa only [mem_closedBall, dist_zero_right] using hx)
  have hgL (x : E) (hx : ‖x‖ ≤ R) (y : E) (hy : ‖y‖ ≤ R) : ‖g x - g y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    have hh := hLip.dist_le_mul x (by simpa only [mem_closedBall, dist_zero_right] using hx)
      y (by simpa only [mem_closedBall, dist_zero_right] using hy)
    simpa only [dist_eq_norm] using hh
  refine ⟨C, hC, ?_⟩
  intro A B hA hB
  have ha (x) : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value A x‖ ≤ R := (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le A x).trans hA
  have hb (x) : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value B x‖ ≤ R := (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le B x).trans hB
  let f : X → F := fun x => segmentAverage g (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x)
  have hf (x) : ‖f x‖ ≤ M := segmentAverage_norm_le g hgM (ha x) (hb x)
  have hh (x y) : ‖f x - f y‖ ≤ ((L : ℝ) * (‖A‖ + ‖B‖)) * (dist x y) ^ α := by
    calc
      _ ≤ (L : ℝ) * (‖OAI.Analysis.Normed.Function.Holder.HolderMap.value A x - OAI.Analysis.Normed.Function.Holder.HolderMap.value A y‖ +
          ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value B x - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y‖) :=
        segmentAverage_sub_le g hg.continuous L.coe_nonneg hgL (ha x) (hb x) (ha y) (hb y)
      _ ≤ (L : ℝ) * (‖A‖ * (dist x y) ^ α + ‖B‖ * (dist x y) ^ α) :=
        mul_le_mul_of_nonneg_left (add_le_add (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le A x y) (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le B x y)) L.coe_nonneg
      _ = _ := by ring
  let fbc : X →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup f
    (continuous_of_holder_bound hα hh) M hf
  let H : OAI.Analysis.Normed.Function.Holder.HolderMap X F α := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le fbc hh
  refine ⟨H, fun _ => rfl, ?_⟩
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα.le (by positivity)
  · intro x
    apply (hf x).trans
    apply hMC.trans
    exact le_mul_of_one_le_right hC (by linarith [norm_nonneg A, norm_nonneg B])
  · intro x y
    apply (hh x y).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
    exact (mul_le_mul_of_nonneg_right hLC (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) hC)

end OAI.Analysis.PDE.Nonlinear
