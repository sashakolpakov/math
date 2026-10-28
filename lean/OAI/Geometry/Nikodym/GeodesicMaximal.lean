import OAI.Geometry.Nikodym.ManifoldMaximal
import OAI.Geometry.Nikodym.GeodesicLength

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

/-- A genuine local geodesic image with prescribed actual Riemannian path
length. No endpoint straightness or model-geodesic condition is assumed. -/
def IsLocalGeodesicImage (ell : ℝ) (J : Set M) : Prop :=
  ∃ (γ : ℝ → M) (v : ℝ → Space n) (I : Set ℝ) (a b : ℝ),
    IsOpen I ∧ IsPreconnected I ∧ a < b ∧ Icc a b ⊆ I ∧
    IsAtlasGeodesic p γ v I ∧ MapsTo γ I C.manifoldChart.source ∧
    J = γ '' Icc a b ∧ J ⊆ C.manifoldPatch (closedBall 0 P.radius) ∧
    pathELength 𝓘(ℝ,Space n) γ a b = ENNReal.ofReal ell

/-- The literal geodesic Nikodym maximal function: ambient metric tubes
around all genuine fixed-length geodesic images in the compact core. -/
def geodesicNikodymMaximal (ell δ : ℝ) (f : M → ℂ) (x : M) : ℝ≥0∞ :=
  ⨆ J : Set M, ⨆ (_ : P.IsLocalGeodesicImage ell J ∧ x ∈ J),
    (∫⁻ y in metricTube δ J, ‖f y‖ₑ ∂atlasRiemannianVolume (n:=n) p) /
      atlasRiemannianVolume (n:=n) p (metricTube δ J)

omit [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem exists_endpoints_of_geodesicImage {ell : ℝ} (hell : 0 < ell)
    {J : Set M} (hJ : P.IsLocalGeodesicImage ell J) :
    ∃ ab : EndpointParameters (Space n) P.radius,
      beltramiSegmentLength κ (ab.1 : Space n) (ab.2 : Space n) = ell ∧
      J = range (endpointCurve C.manifoldChart ab) := by
  obtain ⟨γ,v,I,a,b,hI,hconn,hab,hsub,hgeo,hinside,hJeq,hcore,hlen⟩ := hJ
  have ha : γ a ∈ J := by
    rw [hJeq]
    exact mem_image_of_mem γ (left_mem_Icc.mpr hab.le)
  have hb : γ b ∈ J := by
    rw [hJeq]
    exact mem_image_of_mem γ (right_mem_Icc.mpr hab.le)
  have haend : C.manifoldChart (γ a) ∈ closedBall (0 : Space n) P.radius := by
    rw [← C.manifoldForward_eq (hcore ha).1]
    exact (hcore ha).2
  have hbend : C.manifoldChart (γ b) ∈ closedBall (0 : Space n) P.radius := by
    rw [← C.manifoldForward_eq (hcore hb).1]
    exact (hcore hb).2
  let ab : EndpointParameters (Space n) P.radius :=
    (⟨C.manifoldChart (γ a),haend⟩,⟨C.manifoldChart (γ b),hbend⟩)
  have hpos : 0 < pathELength 𝓘(ℝ,Space n) γ a b := by
    rw [hlen]
    exact ENNReal.ofReal_pos.mpr hell
  have hlen' := C.atlasGeodesic_length_eq hgeo hinside hI hconn hab hsub hpos
  refine ⟨ab,?_,?_⟩
  · have he := congrArg ENNReal.toReal (hlen'.symm.trans hlen)
    simpa only [ENNReal.toReal_ofReal (beltramiSegmentLength_nonneg _ _ _),
      ENNReal.toReal_ofReal hell.le] using he
  · have ht : closedBall (0 : Space n) P.radius ⊆ C.manifoldChart.target := by
      rw [C.manifoldChart_target]
      exact P.core_target
    have himg : C.manifoldChart '' J =
        C.manifoldChart '' range (endpointCurve C.manifoldChart ab) := by
      rw [chart_endpointCurve_range C.manifoldChart ht ab,hJeq]
      exact C.atlasGeodesic_image_eq_segment hgeo hinside hI hconn hab.le hsub
    apply subset_antisymm
    · intro x hx
      have hx' : C.manifoldChart x ∈ C.manifoldChart '' range (endpointCurve C.manifoldChart ab) :=
        himg ▸ mem_image_of_mem C.manifoldChart hx
      obtain ⟨y,hy,hyx⟩ := hx'
      have he : y = x := C.manifoldChart.injOn (P.endpoint_range_core ab hy).1 (hcore hx).1 hyx
      exact he ▸ hy
    · intro x hx
      have hx' : C.manifoldChart x ∈ C.manifoldChart '' J :=
        himg.symm ▸ mem_image_of_mem C.manifoldChart hx
      obtain ⟨y,hy,hyx⟩ := hx'
      have he : y = x := C.manifoldChart.injOn (hcore hy).1 (P.endpoint_range_core ab hx).1 hyx
      exact he ▸ hy

omit [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem geodesicNikodymMaximal_le_endpoint {ell δ : ℝ} (hell : 0 < ell)
    (hδ : δ ≤ P.width) (f : M → ℂ) (x : M) :
    P.geodesicNikodymMaximal ell δ f x ≤ P.endpointNikodymMaximal ell δ f x := by
  rw [P.endpointNikodymMaximal_eq_full ell hδ]
  apply iSup_le
  intro J
  apply iSup_le
  rintro ⟨hJ,hx⟩
  obtain ⟨ab,hlen,himage⟩ := P.exists_endpoints_of_geodesicImage hell hJ
  apply le_iSup_of_le ab
  apply le_iSup_of_le ⟨hlen,himage ▸ hx⟩
  rw [himage]

end OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch
