import OAI.Geometry.Nikodym.Abstract.Geodesic
import OAI.Geometry.Nikodym.InverseGeodesic

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology ContDiff Bundle

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsMetricGeodesic.congr_position {g : SmoothCoordinateMetric E}
    {γ γ' v : ℝ → E} {I : Set ℝ} (h : IsMetricGeodesic g γ v I)
    (hI : IsOpen I) (he : EqOn γ γ' I) : IsMetricGeodesic g γ' v I := by
  refine ⟨?_,?_,?_⟩
  · intro t ht
    apply (h.position_derivative t ht).congr_of_eventuallyEq
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (he hs).symm
  · intro t ht
    simpa only [he ht] using h.velocity_derivative t ht
  · intro t ht
    simpa only [he ht] using h.regular t ht

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

namespace LocalBeltramiChart

variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

/-- The inverse of the constructed manifold chart carries a genuine model
geodesic to a geodesic of the actual Riemannian metric in the original atlas. -/
theorem inverse_atlasGeodesic {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I)
    (hinside : MapsTo γ I C.manifoldChart.target) :
    IsAtlasGeodesic p (C.manifoldChart.symm ∘ γ)
      (fun t => fderiv ℝ (C.chart.symm : E → E) (γ t) (v t)) I := by
  have hi : MapsTo γ I C.chart.target := by
    simpa only [C.manifoldChart_target] using hinside
  refine ⟨fun t ht => C.manifoldChart_source_subset
    (C.manifoldChart.map_target (hinside ht)),?_⟩
  apply (C.inverse_geodesic h hi).congr_position hI
  intro t ht
  change C.chart.symm (γ t) =
    extChartAt 𝓘(ℝ,E) p ((extChartAt 𝓘(ℝ,E) p).symm (C.chart.symm (γ t)))
  symm
  apply (extChartAt 𝓘(ℝ,E) p).right_inv
  exact C.source_domain (C.chart.map_target (hi ht))

end LocalBeltramiChart
end OAI.Geometry.Nikodym
