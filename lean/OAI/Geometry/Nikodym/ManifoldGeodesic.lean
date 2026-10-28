import OAI.Geometry.Nikodym.ManifoldPatch
import OAI.Geometry.Nikodym.Chart.GeodesicSegment

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold
open scoped ContDiff

namespace OAI.Geometry.Nikodym

theorem unitSegment_smul_subset {n : ℕ} {l : ℝ} (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (v c : Space n) : OAI.MeasureTheory.Kakeya.unitSegment (l • v) c ⊆ OAI.MeasureTheory.Kakeya.unitSegment v c := by
  rintro x ⟨t,ht,rfl⟩
  refine ⟨t*l,⟨?_,?_⟩,?_⟩
  · nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t+1/2) hl]
  · nlinarith [mul_nonneg (by linarith [ht.2] : 0 ≤ 1/2-t) hl]
  · rw [smul_smul]

namespace LocalBeltramiChart

variable {n : ℕ} {M : Type*} [PseudoEMetricSpace M]
  [ChartedSpace (Space n) M] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,Space n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Space n) ∞ (Space n)
    (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
  (extChartAt 𝓘(ℝ,Space n) p p))

omit [MeasurableSpace M] [BorelSpace M] in
/-- Actual geodesics, expressed through the constructed Levi-Civita
connection in the ordinary atlas chart, straighten with quantitative length
bounds under the globally measurable manifold chart. -/
theorem manifold_geodesic_segment_representation {γ : ℝ → M} {v : ℝ → Space n}
    {I : Set ℝ}
    (hc : IsMetricGeodesic (abstractChartMetric (E:=Space n) p)
      (fun t => extChartAt 𝓘(ℝ,Space n) p (γ t)) v I)
    (hinside : MapsTo γ I C.manifoldChart.source)
    (hI : IsOpen I) (hconn : IsPreconnected I) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ I)
    (hsmall : ∀ t ∈ Icc a b, |κ| * ‖C.manifoldForward (γ t)‖^2 ≤ 1/2)
    (hunit : ∀ t ∈ Icc a b,
      (abstractChartMetric (E:=Space n) p).inner
        (extChartAt 𝓘(ℝ,Space n) p (γ t)) (v t) (v t) = 1) :
    ∃ (l : ℝ) (w c : Space n), (b-a)/3 ≤ l ∧ l ≤ 4*(b-a) ∧ ‖w‖ = 1 ∧
      C.manifoldForward '' (γ '' Icc a b) = OAI.MeasureTheory.Kakeya.unitSegment (l • w) c := by
  have hs : MapsTo (fun t => extChartAt 𝓘(ℝ,Space n) p (γ t)) I C.chart.source :=
    fun t ht => (hinside ht).2
  have he (t : ℝ) (ht : t ∈ I) :
      C.manifoldForward (γ t) = C.chart (extChartAt 𝓘(ℝ,Space n) p (γ t)) := by
    exact C.manifoldForward_eq (hinside ht)
  obtain ⟨l,w,c,hl,hu,hw,hrep⟩ := C.geodesic_segment_representation hc hs hI hconn
    hab hsub (fun t ht => by simpa only [he t (hsub ht)] using hsmall t ht) hunit
  refine ⟨l,w,c,hl,hu,hw,?_⟩
  rw [← hrep]
  simp only [image_image]
  exact image_congr (fun t ht => he t (hsub ht))

end LocalBeltramiChart
end OAI.Geometry.Nikodym
