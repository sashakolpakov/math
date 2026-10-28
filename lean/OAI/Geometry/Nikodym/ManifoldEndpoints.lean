import OAI.Geometry.Nikodym.ManifoldTubePatch
import OAI.Geometry.Nikodym.EndpointLength
import OAI.Geometry.Nikodym.Chart.GeodesicSegment

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold Metric
open scoped ContDiff

namespace OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Space n) M] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,Space n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Space n) ∞ (Space n)
    (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContinuousRiemannianBundle (Space n) (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Space n) M]
variable {p : M} {κ : ℝ}
variable {C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
  (extChartAt 𝓘(ℝ,Space n) p p)}
variable (P : LocalBeltramiChart.ManifoldTubePatch C)

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem core_target : closedBall (0 : Space n) P.radius ⊆ C.chart.target :=
  (closedBall_subset_closedBall (by linarith [P.radius_pos])).trans P.target

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem endpoint_range_core (ab : EndpointParameters (Space n) P.radius) :
    range (endpointCurve C.manifoldChart ab) ⊆ C.manifoldPatch (closedBall 0 P.radius) := by
  have ht : closedBall (0 : Space n) P.radius ⊆ C.manifoldChart.target := by
    rw [C.manifoldChart_target]
    exact P.core_target
  rintro x ⟨t,rfl⟩
  have hx := endpointCurve_mem_source C.manifoldChart ht ab t
  refine ⟨hx,?_⟩
  rw [mem_preimage,C.manifoldForward_eq hx,chart_endpointCurve C.manifoldChart ht]
  exact (convex_closedBall (0 : Space n) P.radius).lineMap_mem ab.1.property
    ab.2.property t.property

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem endpoint_image (ab : EndpointParameters (Space n) P.radius) :
    C.manifoldForward '' range (endpointCurve C.manifoldChart ab) =
      segment ℝ (ab.1 : Space n) (ab.2 : Space n) := by
  have ht : closedBall (0 : Space n) P.radius ⊆ C.manifoldChart.target := by
    rw [C.manifoldChart_target]
    exact P.core_target
  rw [← chart_endpointCurve_range C.manifoldChart ht ab]
  apply image_congr
  intro x hx
  exact C.manifoldForward_eq (P.endpoint_range_core ab hx).1

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem endpoint_representation {ell : ℝ} (hell : 0 < ell)
    (ab : EndpointParameters (Space n) P.radius)
    (hlen : beltramiSegmentLength κ (ab.1 : Space n) (ab.2 : Space n) = ell) :
    ∃ (l : ℝ) (v c : Space n), ell/3 ≤ l ∧ l ≤ 4*ell ∧ ‖v‖=1 ∧
      C.manifoldForward '' range (endpointCurve C.manifoldChart ab) =
        OAI.MeasureTheory.Kakeya.unitSegment (l • v) c := by
  have hsmall : ∀ y ∈ closedBall (0 : Space n) P.radius, |κ| * ‖y‖^2 ≤ 1/2 :=
    fun y hy => P.small y (closedBall_subset_closedBall (by linarith [P.radius_pos]) hy)
  obtain ⟨hl,hu⟩ := dist_bounds_of_beltramiSegmentLength ab.1.property ab.2.property hsmall hlen
  have hne : (ab.1 : Space n) ≠ ab.2 := by
    intro h
    rw [h,dist_self] at hl
    linarith
  obtain ⟨v,c,hv,hrep⟩ := segment_eq_scaled_unitSegment hne
  exact ⟨_,v,c,hl,hu,hv,(P.endpoint_image ab).trans hrep⟩

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem endpoint_admissible_geometry {ell δ : ℝ} (hell : 0 < ell)
    (hell1 : ell ≤ 1/4) (hδ : δ ≤ P.width)
    (x : M) (ab : EndpointParameters (Space n) P.radius)
    (hadm : beltramiSegmentLength κ (ab.1 : Space n) (ab.2 : Space n) = ell ∧
      x ∈ range (endpointCurve C.manifoldChart ab)) :
    range (endpointCurve C.manifoldChart ab) ⊆ C.manifoldPatch (ball 0 (2*P.radius)) ∧
    x ∈ range (endpointCurve C.manifoldChart ab) ∧
    ∃ (l : ℝ) (v c : Space n), ell/3 ≤ l ∧ l ≤ 1 ∧ ‖v‖=1 ∧
      C.manifoldForward '' range (endpointCurve C.manifoldChart ab) =
        OAI.MeasureTheory.Kakeya.unitSegment (l • v) c ∧
      OAI.MeasureTheory.Kakeya.tube (δ/(P.L : ℝ)) (l • v) c ⊆ ball 0 (2*P.radius) := by
  have hcore := P.endpoint_range_core ab
  refine ⟨hcore.trans (C.manifoldPatch_mono
    (closedBall_subset_ball (by linarith [P.radius_pos]))),hadm.2,?_⟩
  obtain ⟨l,v,c,hl,hu,hv,hrep⟩ := P.endpoint_representation hell ab hadm.1
  refine ⟨l,v,c,hl,by linarith,hv,hrep,P.inner_tube_margin hδ ?_⟩
  rw [← hrep]
  rintro y ⟨z,hz,rfl⟩
  exact (hcore hz).2

end OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch
