import OAI.Geometry.Nikodym.Chart.Neighborhood

noncomputable section
namespace OAI.Geometry.Nikodym.LocalBeltramiChart

open Set Filter Metric
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}
variable (C : LocalBeltramiChart g κ x₀)

/-- The chart and metric comparisons can hold on the same fixed compact
region, with a surrounding ball available for all sufficiently thin tubes. -/
theorem exists_small_biLipschitz_target_ball :
    ∃ (r : ℝ) (K L : NNReal), 0 < r ∧ 1 ≤ K ∧ 1 ≤ L ∧
      closedBall (0 : E) (2*r) ⊆ C.chart.target ∧
      (∀ x ∈ closedBall (0 : E) (2*r), |κ| * ‖x‖^2 ≤ 1/2) ∧
      LipschitzOnWith K (C.chart : E → E)
        (C.chart.symm '' closedBall (0 : E) (2*r)) ∧
      LipschitzOnWith L (C.chart.symm : E → E) (closedBall (0 : E) (2*r)) ∧
      IsCompact (C.chart.symm '' closedBall (0 : E) (2*r)) ∧
      C.chart.symm '' closedBall (0 : E) (2*r) ⊆ C.chart.source := by
  obtain ⟨r,K,L,hr,hK,hL,ht,hf,hb,hc,hs⟩ := C.exists_biLipschitz_target_ball
  have hcont : ContinuousAt (fun x : E => |κ| * ‖x‖^2) 0 := by fun_prop
  have hneigh : {x : E | |κ| * ‖x‖^2 < 1/2} ∈ 𝓝 (0 : E) :=
    hcont.preimage_mem_nhds (Iio_mem_nhds (by simp))
  obtain ⟨s,hsp,hss⟩ := Metric.mem_nhds_iff.mp hneigh
  let r' := min r (s/4)
  have hr' : 0 < r' := lt_min hr (div_pos hsp (by norm_num))
  have hsub : closedBall (0 : E) (2*r') ⊆ closedBall 0 (2*r) :=
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  have hball : closedBall (0 : E) (2*r') ⊆ ball 0 s :=
    closedBall_subset_ball (by dsimp [r']; have := min_le_right r (s/4); linarith)
  refine ⟨r',K,L,hr',hK,hL,hsub.trans ht,?_,hf.mono (image_mono hsub),hb.mono hsub,?_,
    (image_mono hsub).trans hs⟩
  · intro x hx
    exact (hss (hball hx)).le
  · exact (isCompact_closedBall (0 : E) (2*r')).image_of_continuousOn
      (C.inverse_smooth.continuousOn.mono (hsub.trans ht))

end OAI.Geometry.Nikodym.LocalBeltramiChart
