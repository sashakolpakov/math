import OAI.Geometry.Nikodym.ManifoldGeodesic
import OAI.Geometry.Nikodym.Abstract.ChartVolume
import OAI.Geometry.Nikodym.DimensionChart
import OAI.Analysis.Fourier.LocalSmoothing.FurtherResults

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Metric
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {n : ℕ} {M : Type*} [EMetricSpace M]
  [ChartedSpace (Space n) M] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,Space n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Space n) ∞ (Space n)
    (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContinuousRiemannianBundle (Space n) (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Space n) M]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
  (extChartAt 𝓘(ℝ,Space n) p p))

/-- Positive-length intersections with genuine unit-speed geodesic
segments in the compact core. The differential equation uses the actual
Levi-Civita connection of the atlas pullback metric. -/
def HasLocalGeodesicIncidences (r ell η : ℝ) (A Ω : Set M) : Prop :=
  ∀ x ∈ Ω, ∃ (γ : ℝ → M) (v : ℝ → Space n) (I : Set ℝ),
    IsOpen I ∧ IsPreconnected I ∧ Icc 0 ell ⊆ I ∧
    IsMetricGeodesic (abstractChartMetric (E:=Space n) p)
      (fun t => extChartAt 𝓘(ℝ,Space n) p (γ t)) v I ∧
    MapsTo γ I C.manifoldChart.source ∧
    γ '' Icc 0 ell ⊆ C.manifoldPatch (closedBall 0 r) ∧
    x ∈ γ '' Icc 0 ell ∧
    ENNReal.ofReal η ≤ Measure.hausdorffMeasure 1 (A ∩ (γ '' Icc 0 ell)) ∧
    ∀ t ∈ Icc 0 ell, (abstractChartMetric (E:=Space n) p).inner
      (extChartAt 𝓘(ℝ,Space n) p (γ t)) (v t) (v t) = 1

/-- The local Nikodym dimension conclusion, with ambient Riemannian
Hausdorff measure and distance and actual Riemannian volume. There is no
Euclidean Nikodym or chart-comparison hypothesis. -/
theorem exists_local_nikodym_dimension (hn : 2 ≤ n) :
    ∃ r : ℝ, 0 < r ∧ closedBall (0 : Space n) (2*r) ⊆ C.chart.target ∧
      ∀ (A Ω : Set M) (ell η : ℝ), 0 < ell → ell ≤ 1/4 → 0 < η →
        MeasurableSet Ω → 0 < atlasRiemannianVolume (n:=n) p Ω →
        C.HasLocalGeodesicIncidences r ell η A Ω →
        dimH (A ∩ C.manifoldPatch (ball 0 (2*r))) = n := by
  obtain ⟨r,K,L,hr,hK,hL,ht,hs,hf,hi,hcompact,hopen,hbase⟩ :=
    C.exists_manifold_controlled_patch
  have hcore : closedBall (0 : Space n) r ⊆ ball 0 (2*r) :=
    closedBall_subset_ball (by linarith)
  have hcore' : closedBall (0 : Space n) r ⊆ closedBall 0 (2*r) :=
    hcore.trans ball_subset_closedBall
  refine ⟨r,hr,ht,?_⟩
  intro A Ω ell η hell hell1 hη hΩ hΩpos hinc
  have hΩcore : Ω ⊆ C.manifoldPatch (closedBall 0 r) := by
    intro x hx
    obtain ⟨γ,v,I,hI,hconn,hsub,hgeo,hinside,hγ,hxγ,hint,hunit⟩ := hinc x hx
    exact hγ hxγ
  have hΩsource : Ω ⊆ C.manifoldChart.source := fun x hx => (hΩcore hx).1
  have hpos : 0 < volume (C.manifoldForward '' Ω) :=
    C.volume_manifoldForward_image_pos hΩ hΩsource (by
      rintro y ⟨x,hx,rfl⟩
      exact hs _ (hcore' (hΩcore hx).2)) hΩpos
  apply nikodym_dimension_in_chart OAI.Analysis.Fourier.LocalSmoothing.nikodym_maximal hn hf
    (hi.mono ball_subset_closedBall) (fun x hx => hx.2)
    (fun x hx => C.manifoldInverse_forward hx.1) (lt_of_lt_of_le zero_lt_one hL)
    (C.measurableSet_manifoldForward_image hΩ hΩsource) hpos hη
  intro x hx
  obtain ⟨γ,v,I,hI,hconn,hsub,hgeo,hinside,hγ,hxγ,hint,hunit⟩ := hinc x hx
  obtain ⟨l,w,c,hl,hu,hw,hrep⟩ := C.manifold_geodesic_segment_representation hgeo
    hinside hI hconn hell hsub (by
      intro t ht'
      exact hs _ (hcore' (hγ (mem_image_of_mem γ ht')).2)) hunit
  refine ⟨γ '' Icc 0 ell,(fun y hy => C.manifoldPatch_mono hcore (hγ hy)),
    hxγ,hint,w,c,hw,?_⟩
  rw [hrep]
  apply unitSegment_smul_subset
  · linarith
  · linarith

end OAI.Geometry.Nikodym.LocalBeltramiChart
