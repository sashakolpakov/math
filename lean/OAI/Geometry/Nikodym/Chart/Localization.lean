import OAI.Geometry.Nikodym.Chart.SmallNeighborhood

noncomputable section
namespace OAI.Geometry.Nikodym.LocalBeltramiChart

open Set Filter Metric
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}
variable (C : LocalBeltramiChart g κ x₀)

omit [FiniteDimensional ℝ E] in
/-- Model neighborhoods can be chosen inside any prescribed physical
neighborhood, in particular a convex intrinsic-coordinate metric ball. -/
theorem exists_target_ball_inside {U : Set E} (hU : U ∈ 𝓝 x₀) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : E) (2*r) ⊆ C.chart.target ∧
      C.chart.symm '' closedBall (0 : E) (2*r) ⊆ U := by
  have hi := (C.inverse_smooth 0 C.center_mem_target).contDiffAt
    (C.chart.open_target.mem_nhds C.center_mem_target)
  have hpre : C.chart.symm ⁻¹' U ∈ 𝓝 (0 : E) := by
    apply hi.continuousAt.preimage_mem_nhds
    simpa only [C.inverse_center] using hU
  have hgood := inter_mem (C.chart.open_target.mem_nhds C.center_mem_target) hpre
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hsub : closedBall (0 : E) (2*(s/4)) ⊆ ball 0 s :=
    closedBall_subset_ball (by linarith)
  refine ⟨s/4,by positivity,fun y hy => (hball (hsub hy)).1,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  exact (hball (hsub hy)).2

end OAI.Geometry.Nikodym.LocalBeltramiChart
