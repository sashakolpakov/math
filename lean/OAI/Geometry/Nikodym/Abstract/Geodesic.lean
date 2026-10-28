import OAI.Geometry.Nikodym.Abstract.ChartMetric
import OAI.Geometry.Nikodym.Chart.GeodesicSegment

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold Filter
open scoped Topology ContDiff Bundle RealInnerProductSpace

namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

/-- The ordinary coordinate definition of a local Riemannian geodesic:
its atlas coordinate path solves the Levi-Civita equation of the actual
pulled-back metric. No straightening or model-metric premise occurs. -/
structure IsAtlasGeodesic (p : M) (γ : ℝ → M) (v : ℝ → E) (I : Set ℝ) : Prop where
  source : MapsTo γ I (chartAt E p).source
  equation : IsMetricGeodesic (abstractChartMetric (E:=E) p)
    ((extChartAt 𝓘(ℝ,E) p) ∘ γ) v I

namespace LocalBeltramiChart

variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

theorem manifold_geodesic_image_in_line {γ : ℝ → M} {v : ℝ → E} {I : Set ℝ}
    (hγ : IsAtlasGeodesic p γ v I) (hinside : MapsTo γ I C.manifoldChart.source)
    (hI : IsOpen I) (hconn : IsPreconnected I) {t₀ : ℝ} (ht₀ : t₀ ∈ I) :
    ∃ c : E, ∀ t ∈ I, ∃ s : ℝ,
      C.manifoldChart (γ t) = C.manifoldChart (γ t₀) + s • c := by
  exact C.geodesic_image_in_line hγ.equation (fun t ht => (hinside ht).2) hI hconn ht₀

end LocalBeltramiChart

section Segment
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Space n) M]
  [IsManifold 𝓘(ℝ,Space n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Space n) ∞ (Space n)
    (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
variable {p : M} {κ : ℝ}

theorem LocalBeltramiChart.atlasGeodesic_segment_representation
    (C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
      (extChartAt 𝓘(ℝ,Space n) p p))
    {γ : ℝ → M} {v : ℝ → Space n} {I : Set ℝ}
    (hγ : IsAtlasGeodesic p γ v I) (hinside : MapsTo γ I C.manifoldChart.source)
    (hI : IsOpen I) (hconn : IsPreconnected I) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ I)
    (hsmall : ∀ t ∈ Icc a b, |κ| * ‖C.manifoldChart (γ t)‖^2 ≤ 1/2)
    (hunit : ∀ t ∈ Icc a b, (abstractChartMetric (E:=Space n) p).inner
      (extChartAt 𝓘(ℝ,Space n) p (γ t)) (v t) (v t) = 1) :
    ∃ (l : ℝ) (w c : Space n), (b-a)/3 ≤ l ∧ l ≤ 4*(b-a) ∧ ‖w‖ = 1 ∧
      C.manifoldChart '' (γ '' Icc a b) = OAI.MeasureTheory.Kakeya.unitSegment (l • w) c := by
  obtain ⟨l,w,c,hl,hu,hw,he⟩ := C.geodesic_segment_representation hγ.equation
    (fun t ht => (hinside ht).2) hI hconn hab hsub hsmall hunit
  refine ⟨l,w,c,hl,hu,hw,?_⟩
  change (C.chart ∘ extChartAt 𝓘(ℝ,Space n) p) '' (γ '' Icc a b) = _
  simpa only [←image_comp,Function.comp_assoc] using he

end Segment
end OAI.Geometry.Nikodym
