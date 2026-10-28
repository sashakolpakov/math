import OAI.Geometry.Nikodym.Abstract.ChartMetric
import OAI.Geometry.Nikodym.IsometryBeltrami

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The explicit Beltrami equation is the geodesic equation of its actual
smooth positive metric. -/
theorem IsBeltramiGeodesic.toMetricGeodesic
    {κ : ℝ} {γ v : ℝ → E} {I : Set ℝ} (h : IsBeltramiGeodesic κ γ v I) :
    IsMetricGeodesic (beltramiSmoothMetric κ) γ v I := by
  refine ⟨h.position_derivative,?_,h.regular⟩
  intro t ht
  simpa only [beltramiSmoothMetric_christoffel (h.regular t ht)] using
    h.velocity_derivative t ht

namespace LocalBeltramiChart

variable {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}

omit [FiniteDimensional ℝ E] in
/-- The inverse chart derivative is onto, as follows from differentiating
the genuine chart inverse identity. -/
theorem inverse_derivative_surjective (C : LocalBeltramiChart g κ x₀)
    {y : E} (hy : y∈C.chart.target) :
    Function.Surjective (fderiv ℝ (C.chart.symm : E → E) y) := by
  have hx := C.chart.map_target hy
  have hf := ((C.smooth _ hx).contDiffAt
    (C.chart.open_source.mem_nhds hx)).differentiableAt (by simp)
  have hi := ((C.inverse_smooth _ hy).contDiffAt
    (C.chart.open_target.mem_nhds hy)).differentiableAt (by simp)
  have he : (C.chart.symm : E → E) ∘ C.chart =ᶠ[𝓝 (C.chart.symm y)] id := by
    filter_upwards [C.chart.open_source.mem_nhds hx] with z hz
    exact C.chart.left_inv hz
  have hd := he.fderiv_eq (𝕜:=ℝ)
  have hi' : DifferentiableAt ℝ (C.chart.symm : E → E) (C.chart (C.chart.symm y)) := by
    simpa only [C.chart.right_inv hy] using hi
  rw [fderiv_comp _ hi' hf,C.chart.right_inv hy,fderiv_id] at hd
  intro w
  refine ⟨fderiv ℝ (C.chart : E → E) (C.chart.symm y) w,?_⟩
  exact congrArg (fun L : E →L[ℝ] E => L w) hd

/-- Pulling a Beltrami geodesic back by the constructed local chart gives a
genuine geodesic of the original metric, with its actual differentiated
velocity. No image-straightening or inverse-derivative premise is assumed. -/
theorem inverse_geodesic (C : LocalBeltramiChart g κ x₀)
    {γ v : ℝ → E} {I : Set ℝ} (h : IsBeltramiGeodesic κ γ v I)
    (hinside : MapsTo γ I C.chart.target) :
    IsMetricGeodesic g (fun t => C.chart.symm (γ t))
      (fun t => fderiv ℝ (C.chart.symm : E → E) (γ t) (v t)) I := by
  apply h.toMetricGeodesic.map_local_isometry
  · intro t ht
    exact C.source_domain (C.chart.map_target (hinside ht))
  · intro t ht
    exact ((C.inverse_smooth _ (hinside ht)).contDiffAt
      (C.chart.open_target.mem_nhds (hinside ht))).of_le (by simp)
  · intro t ht
    exact C.inverse_derivative_surjective (hinside ht)
  · intro t ht
    filter_upwards [C.chart.open_target.mem_nhds (hinside ht)] with y hy
    intro u w
    rw [beltramiSmoothMetric_inner]
    exact (C.inverse_metric hy u w).symm

end LocalBeltramiChart
end OAI.Geometry.Nikodym
