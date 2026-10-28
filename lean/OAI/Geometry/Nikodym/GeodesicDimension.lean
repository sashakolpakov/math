import OAI.Geometry.Nikodym.GeodesicMaximal
import OAI.Geometry.Nikodym.Abstract.ChartVolume
import OAI.Geometry.Nikodym.DimensionChart
import OAI.Geometry.Nikodym.ManifoldGeodesic
import OAI.Analysis.Fourier.LocalSmoothing.FurtherResults

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Metric
open scoped ContDiff ENNReal

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
theorem isLocalGeodesicImage_subset_core {ell : ℝ} {J : Set M}
    (hJ : P.IsLocalGeodesicImage ell J) :
    J ⊆ C.manifoldPatch (closedBall 0 P.radius) := by
  obtain ⟨γ,v,I,a,b,hI,hconn,hab,hsub,hgeo,hinside,hJeq,hcore,hlen⟩ := hJ
  exact hcore

omit [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
/-- The dimension conclusion for genuine geodesic images of fixed actual
Riemannian length, with no chosen unit-speed parameterization required. -/
theorem geodesic_incidence_dimension (hn : 2 ≤ n)
    {A Ω : Set M} {ell η : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1/4)
    (hη : 0 < η) (hΩ : MeasurableSet Ω)
    (hΩpos : 0 < atlasRiemannianVolume (n:=n) p Ω)
    (hinc : ∀ x ∈ Ω, ∃ J : Set M,
      P.IsLocalGeodesicImage ell J ∧ x ∈ J ∧
      ENNReal.ofReal η ≤ Measure.hausdorffMeasure 1 (A ∩ J)) :
    dimH (A ∩ C.manifoldPatch (ball 0 (2*P.radius))) = n := by
  have hcore : closedBall (0 : Space n) P.radius ⊆ ball 0 (2*P.radius) :=
    closedBall_subset_ball (by linarith [P.radius_pos])
  have hΩcore : Ω ⊆ C.manifoldPatch (closedBall 0 P.radius) := by
    intro x hx
    obtain ⟨J,hJ,hxJ,hint⟩ := hinc x hx
    exact P.isLocalGeodesicImage_subset_core hJ hxJ
  have hΩsource : Ω ⊆ C.manifoldChart.source := fun x hx => (hΩcore hx).1
  have hpos : 0 < volume (C.manifoldForward '' Ω) :=
    C.volume_manifoldForward_image_pos hΩ hΩsource (by
      rintro y ⟨x,hx,rfl⟩
      exact P.small _ (ball_subset_closedBall (hcore (hΩcore hx).2))) hΩpos
  apply nikodym_dimension_in_chart OAI.Analysis.Fourier.LocalSmoothing.nikodym_maximal hn P.forward_lipschitz
    (P.inverse_lipschitz.mono ball_subset_closedBall) (fun x hx => hx.2)
    (fun x hx => C.manifoldInverse_forward hx.1)
    (lt_of_lt_of_le zero_lt_one P.one_le_L)
    (C.measurableSet_manifoldForward_image hΩ hΩsource) hpos hη
  intro x hx
  obtain ⟨J,hJ,hxJ,hint⟩ := hinc x hx
  obtain ⟨ab,hlen,himage⟩ := P.exists_endpoints_of_geodesicImage hell hJ
  obtain ⟨l,v,c,hl,hu,hv,hrep⟩ := P.endpoint_representation hell ab hlen
  refine ⟨J,(P.isLocalGeodesicImage_subset_core hJ).trans
    (C.manifoldPatch_mono hcore),hxJ,hint,v,c,hv,?_⟩
  rw [himage,hrep]
  apply unitSegment_smul_subset
  · linarith
  · linarith

end OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch
