import OAI.Geometry.Nikodym.GeodesicMaximal
import OAI.Geometry.Nikodym.SegmentGeodesic

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
theorem isLocalGeodesicImage_endpoint {ell : ℝ}
    (ab : EndpointParameters (Space n) P.radius)
    (hlen : beltramiSegmentLength κ (ab.1 : Space n) (ab.2 : Space n) = ell) :
    P.IsLocalGeodesicImage ell (range (endpointCurve C.manifoldChart ab)) := by
  have ht : closedBall (0 : Space n) P.radius ⊆ C.manifoldChart.target := by
    rw [C.manifoldChart_target]
    exact P.core_target
  have hseg : segment ℝ (ab.1 : Space n) (ab.2 : Space n) ⊆ C.manifoldChart.target :=
    (convex_closedBall (0 : Space n) P.radius).segment_subset ab.1.property ab.2.property |>.trans ht
  have himage : C.manifoldChart.symm '' segment ℝ (ab.1 : Space n) (ab.2 : Space n) =
      range (endpointCurve C.manifoldChart ab) := by
    rw [← chart_endpointCurve_range C.manifoldChart ht ab]
    apply subset_antisymm
    · rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
      rwa [C.manifoldChart.left_inv (P.endpoint_range_core ab hz).1]
    · intro x hx
      exact ⟨C.manifoldChart x,⟨x,hx,rfl⟩,
        C.manifoldChart.left_inv (P.endpoint_range_core ab hx).1⟩
  obtain ⟨γ,v,I,T,hI,hconn,hT,hsub,hgeo,hinside,hγ,hlenγ⟩ :=
    C.exists_inverse_segment_geodesic hseg
  refine ⟨γ,v,I,0,T,hI,hconn,hT,hsub,hgeo,hinside,
    (hγ.trans himage).symm,P.endpoint_range_core ab,?_⟩
  exact hlenγ.trans (congrArg ENNReal.ofReal hlen)

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem isLocalGeodesicImage_iff_endpoints {ell : ℝ} (hell : 0 < ell)
    {J : Set M} : P.IsLocalGeodesicImage ell J ↔
      ∃ ab : EndpointParameters (Space n) P.radius,
        beltramiSegmentLength κ (ab.1 : Space n) (ab.2 : Space n) = ell ∧
        J = range (endpointCurve C.manifoldChart ab) := by
  constructor
  · exact P.exists_endpoints_of_geodesicImage hell
  · rintro ⟨ab,hlen,rfl⟩
    exact P.isLocalGeodesicImage_endpoint ab hlen

omit [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem endpointNikodymMaximal_le_geodesic {ell δ : ℝ}
    (hδ : δ ≤ P.width) (f : M → ℂ) (x : M) :
    P.endpointNikodymMaximal ell δ f x ≤ P.geodesicNikodymMaximal ell δ f x := by
  rw [P.endpointNikodymMaximal_eq_full ell hδ]
  apply iSup_le
  intro ab
  apply iSup_le
  rintro ⟨hlen,hx⟩
  apply le_iSup_of_le (range (endpointCurve C.manifoldChart ab))
  exact le_iSup_of_le ⟨P.isLocalGeodesicImage_endpoint ab hlen,hx⟩ le_rfl

omit [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
/-- Endpoint parametrization and the literal supremum over genuine
fixed-Riemannian-length geodesics define exactly the same operator. -/
theorem geodesicNikodymMaximal_eq_endpoint {ell δ : ℝ}
    (hell : 0 < ell) (hδ : δ ≤ P.width) (f : M → ℂ) :
    P.geodesicNikodymMaximal ell δ f = P.endpointNikodymMaximal ell δ f := by
  funext x
  exact le_antisymm (P.geodesicNikodymMaximal_le_endpoint hell hδ f x)
    (P.endpointNikodymMaximal_le_geodesic hδ f x)

theorem measurable_geodesicNikodymMaximal {ell δ : ℝ}
    (hell : 0 < ell) (hδ : 0 < δ) (hδP : δ ≤ P.width)
    (f : M → ℂ) (hf : Integrable f ((atlasRiemannianVolume (n:=n) p).restrict
      (C.manifoldPatch (ball 0 (2*P.radius))))) :
    Measurable (P.geodesicNikodymMaximal ell δ f) := by
  rw [P.geodesicNikodymMaximal_eq_endpoint hell hδP]
  exact P.measurable_endpointNikodymMaximal ell hδ f hf

/-- The local Nikodym estimate for the literal geodesic maximal operator,
using ambient Riemannian tubes, volume, and the actual geodesic length. -/
theorem geodesicNikodymMaximal_bound (hn : 2 ≤ n)
    {ε ell : ℝ} (hε : 0 < ε) (hell : 0 < ell) (hell1 : ell ≤ 1/4) :
    ∃ B : ℝ, 0 < B ∧ ∀ δ : ℝ, 0 < δ → δ ≤ P.width → ∀ f : M → ℂ,
      MemLp f n ((atlasRiemannianVolume (n:=n) p).restrict
        (C.manifoldPatch (ball 0 (2*P.radius)))) →
      MemLp (P.geodesicNikodymMaximal ell δ f) n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) ∧
      eLpNorm (P.geodesicNikodymMaximal ell δ f) n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) ≤
      ENNReal.ofReal (B*δ^(-ε))*eLpNorm f n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) := by
  obtain ⟨B,hB,hbound⟩ := P.endpointNikodymMaximal_bound hn hε hell hell1
  refine ⟨B,hB,?_⟩
  intro δ hδ hδP f hf
  rw [P.geodesicNikodymMaximal_eq_endpoint hell hδP]
  exact hbound δ hδ hδP f hf

end OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch
