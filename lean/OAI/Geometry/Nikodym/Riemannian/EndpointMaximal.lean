import OAI.Geometry.Nikodym.Riemannian.TubeMeasure
import OAI.Geometry.Nikodym.EndpointMeasurability
import OAI.Geometry.Nikodym.Abstract.VolumePositive

noncomputable section
open Set Metric _root_.MeasureTheory Manifold Bundle
open scoped ContDiff ENNReal Topology
namespace OAI.Geometry.Nikodym

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
  [IsRiemannianManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]

/-- Measurability of the genuine endpoint-geodesic maximal operator, using
the actual ambient Riemannian distance and determinant volume. Neither a
measurable supremum nor null distance spheres are hypotheses. -/
theorem measurable_atlas_endpoint_metric_maximal
    (p : M) {S : Set M} (hS : IsOpen S)
    (hSS : S⊆(extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source)
    [IsFiniteMeasure ((atlasRiemannianVolume (n:=n) p).restrict S)]
    (H : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {r : ℝ}
    (hr : closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ H.target)
    (hmeet : ∀ ab : EndpointParameters (EuclideanSpace ℝ (Fin n)) r,
      (range (endpointCurve H ab) ∩ S).Nonempty)
    {δ : ℝ} (hδ : 0<δ)
    {A : Set (EndpointParameters (EuclideanSpace ℝ (Fin n)) r)} (hA : IsClosed A)
    (f : M → ℂ) (hf : Integrable f ((atlasRiemannianVolume (n:=n) p).restrict S)) :
    Measurable (metricTubeMaximal (atlasRiemannianVolume (n:=n) p) S
      (fun _ ab => range (endpointCurve H ab))
      (fun x ab => ab∈A ∧ x∈range (endpointCurve H ab)) δ f) := by
  let : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0,by norm_num⟩⟩
  apply measurable_endpoint_metric_maximal _ S H hr δ
    (fun ab => atlasRiemannianVolume_restrict_distance_level_null p S
      (range_nonempty _) hδ) _ hA f hf
  intro ab
  exact (atlasRiemannianVolume_metricTube_pos p hS hSS hδ (hmeet ab)).ne'

end OAI.Geometry.Nikodym
