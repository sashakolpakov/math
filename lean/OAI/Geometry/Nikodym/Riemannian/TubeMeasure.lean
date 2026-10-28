import OAI.Geometry.Riemannian.NikodymRiemannianLevelNull
import OAI.Geometry.Nikodym.Riemannian.LocalNullMeasure
import OAI.Geometry.Nikodym.SublevelMaximal
import OAI.Geometry.Nikodym.CompactCurveDistance
import OAI.Geometry.Nikodym.CurveDistanceSlice

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

/-- Every positive distance level has zero genuine coordinate Riemannian
volume. This uses the ambient Riemannian distance without assuming geodesic
completeness or convexity of the atlas chart. -/
theorem atlasRiemannianVolume_distance_level_null (p : M)
    {A : Set M} (hA : A.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    atlasRiemannianVolume (n:=n) p {x | infDist x A=δ} = 0 := by
  apply atlasRiemannianVolume_null_of_locally_centered_chart_null p
    (isClosed_eq (continuous_infDist_pt A) continuous_const).measurableSet
  intro x hx
  exact OAI.Geometry.Riemannian.exists_distance_level_coordinate_haar_null volume x hA hδ

theorem atlasRiemannianVolume_restrict_distance_level_null (p : M) (S : Set M)
    {A : Set M} (hA : A.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    (atlasRiemannianVolume (n:=n) p).restrict S {x | infDist x A=δ} = 0 :=
  Measure.absolutelyContinuous_restrict (atlasRiemannianVolume_distance_level_null p hA hδ)

/-- Genuine ambient-metric tubes around a continuous compact family have
continuous Riemannian volume in every finite-volume observation region. -/
theorem continuous_atlasRiemannianVolume_tubes
    {P J : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace J] [CompactSpace J] [Nonempty J]
    (p : M) (S : Set M)
    [IsFiniteMeasure ((atlasRiemannianVolume (n:=n) p).restrict S)]
    (γ : P × J → M) (hγ : Continuous γ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun q => (atlasRiemannianVolume (n:=n) p).restrict S
      (metricTube δ (range (fun t => γ (q,t))))) := by
  simp_rw [metricTube_eq_infDist_sublevel (range_nonempty _)]
  have hd (x : M) : Continuous (fun q => infDist x (range (fun t => γ (q,t)))) :=
    continuous_infDist_range_parameter γ hγ x
  exact continuous_volume_strict_sublevel _
    (fun q x => infDist x (range (fun t => γ (q,t)))) δ
    hd
    (fun q => (continuous_infDist_pt _).measurable)
    (fun q => atlasRiemannianVolume_restrict_distance_level_null p S (range_nonempty _) hδ)

end OAI.Geometry.Nikodym
