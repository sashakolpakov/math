import OAI.Geometry.Nikodym.ManifoldDimension
import OAI.Geometry.Nikodym.Abstract.Sectional

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Metric
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym

open OAI.Geometry.Nikodym

/-- The constant-curvature manifold Nikodym dimension conclusion from
`sections/further_geometry.tex`. The straightening chart is constructed
from scalar sectional curvature; it is not an additional hypothesis.
Hausdorff dimension and incidence measure use the ambient Riemannian
distance, and positive volume uses the metric's determinant density. -/
theorem local_nikodym_dimension
    {n : ℕ} {M : Type*} [EMetricSpace M]
    [ChartedSpace (Space n) M] [MeasurableSpace M] [BorelSpace M]
    [IsManifold 𝓘(ℝ,Space n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,Space n) ∞ (Space n)
      (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
    [IsContinuousRiemannianBundle (Space n) (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
    [IsRiemannianManifold 𝓘(ℝ,Space n) M]
    (hn : 2 ≤ n) (p : M) {κ : ℝ}
    (hκ : (abstractChartMetric (E:=Space n) p).HasConstantSectionalCurvature κ) :
    ∃ (C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
        (extChartAt 𝓘(ℝ,Space n) p p)) (r : ℝ),
      0 < r ∧ closedBall (0 : Space n) (2*r) ⊆ C.chart.target ∧
      IsOpen (C.manifoldPatch (ball 0 (2*r))) ∧
      p ∈ C.manifoldPatch (ball 0 (2*r)) ∧
      IsCompact (closure (C.manifoldPatch (ball 0 (2*r)))) ∧
      ∀ (A Ω : Set M) (ell η : ℝ), 0 < ell → ell ≤ 1/4 → 0 < η →
        MeasurableSet Ω → 0 < atlasRiemannianVolume (n:=n) p Ω →
        C.HasLocalGeodesicIncidences r ell η A Ω →
        dimH (A ∩ C.manifoldPatch (ball 0 (2*r))) = n := by
  obtain ⟨C⟩ := nonempty_manifold_localBeltramiChart p hκ
  obtain ⟨r,hr,ht,h⟩ := C.exists_local_nikodym_dimension hn
  have hi : ContinuousOn C.manifoldInverse (closedBall (0 : Space n) (2*r)) := by
    apply C.manifoldChart.symm.continuousOn.congr_mono
      (fun y hy => C.manifoldInverse_eq (ht hy))
    change closedBall (0 : Space n) (2*r) ⊆ C.manifoldChart.target
    rw [C.manifoldChart_target]
    exact ht
  have hcompact : IsCompact (C.manifoldPatch (closedBall (0 : Space n) (2*r))) := by
    rw [←C.manifoldInverse_image ht]
    exact (isCompact_closedBall (0 : Space n) (2*r)).image_of_continuousOn hi
  have hclosure : IsCompact (closure (C.manifoldPatch (ball 0 (2*r)))) :=
    hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (C.manifoldPatch_mono ball_subset_closedBall) hcompact.isClosed)
  refine ⟨C,r,hr,ht,C.isOpen_manifoldPatch isOpen_ball,?_,hclosure,h⟩
  refine ⟨C.manifoldChart_base_mem,?_⟩
  rw [mem_preimage,C.manifoldForward_eq C.manifoldChart_base_mem,C.manifoldChart_base_value]
  exact mem_ball_self (mul_pos (by norm_num) hr)

end OAI.Geometry.Nikodym
