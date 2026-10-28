import OAI.Geometry.Nikodym.Sectional.MetricDerivative

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

/-- Curvature of the metric-derived connection is skew-adjoint for the
metric. This is obtained by commuting two actual coefficient derivatives. -/
theorem curvature_metric_skew {x : E} (hx : x ∈ g.domain) (a b w z : E) :
    g.inner x (g.curvature x a b w) z + g.inner x w (g.curvature x a b z) = 0 := by
  have hg := (g.smooth x hx).contDiffAt (g.isOpen_domain.mem_nhds hx)
  have hs : ⟪fderiv ℝ (fderiv ℝ g.coefficient) x a b w,z⟫ =
      ⟪fderiv ℝ (fderiv ℝ g.coefficient) x b a w,z⟫ :=
    congrArg (fun L : E →L[ℝ] E => ⟪L w,z⟫)
      (hg.isSymmSndFDerivAt (by simp) a b)
  have h1 := g.second_metric_compatibility hx a b w z
  have h2 := g.second_metric_compatibility hx b a w z
  rw [hs] at h1
  rw [← g.christoffel_compatible hx a (g.christoffel x b w) z,
    ← g.christoffel_compatible hx a w (g.christoffel x b z)] at h1
  rw [← g.christoffel_compatible hx b (g.christoffel x a w) z,
    ← g.christoffel_compatible hx b w (g.christoffel x a z)] at h2
  simp only [SmoothCoordinateMetric.curvature,SmoothCoordinateMetric.inner,map_add,map_sub,inner_add_left,inner_sub_left,
    inner_add_right,inner_sub_right] at h1 h2 ⊢
  linarith

theorem curvature_inner_swap_last {x : E} (hx : x ∈ g.domain) (a b w z : E) :
    g.inner x (g.curvature x a b w) z = -g.inner x (g.curvature x a b z) w := by
  have hh := g.curvature_metric_skew hx a b w z
  have hs : g.inner x w (g.curvature x a b z) = g.inner x (g.curvature x a b z) w :=
    (g.symmetric x hx w _).trans (real_inner_comm _ _)
  rw [hs] at hh
  linarith

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
