import OAI.Geometry.Nikodym.Chart.Neighborhood
import OAI.Geometry.Nikodym.Beltrami.SegmentBounds

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped ContDiff

theorem segment_eq_centered_unitSegment {n : ℕ} (a b : Space n) :
    segment ℝ a b = OAI.MeasureTheory.Kakeya.unitSegment (b-a) ((1/2 : ℝ) • (a+b)) := by
  rw [segment_eq_image']
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨t-1/2,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    module
  · rintro ⟨t,ht,rfl⟩
    refine ⟨t+1/2,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    module

theorem segment_eq_scaled_unitSegment {n : ℕ} {a b : Space n} (hab : a ≠ b) :
    ∃ v c : Space n, ‖v‖ = 1 ∧
      segment ℝ a b = OAI.MeasureTheory.Kakeya.unitSegment (dist a b • v) c := by
  have hn : 0 < ‖b-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  refine ⟨‖b-a‖⁻¹ • (b-a),(1/2 : ℝ) • (a+b),?_,?_⟩
  · simp [norm_smul,hn.ne']
  · have he : dist a b • (‖b-a‖⁻¹ • (b-a)) = b-a := by
      rw [dist_eq_norm,norm_sub_rev,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
    rw [he]
    exact segment_eq_centered_unitSegment a b

namespace LocalBeltramiChart

variable {n : ℕ} {g : SmoothCoordinateMetric (Space n)} {κ : ℝ} {x₀ : Space n}
variable (C : LocalBeltramiChart g κ x₀)

/-- Actual unit-speed geodesic segments straighten to Euclidean segments
with a uniform positive length range. -/
theorem geodesic_segment_representation {γ v : ℝ → Space n} {I : Set ℝ}
    (hc : IsMetricGeodesic g γ v I) (hinside : MapsTo γ I C.chart.source)
    (hI : IsOpen I) (hconn : IsPreconnected I) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ I)
    (hsmall : ∀ t ∈ Icc a b, |κ| * ‖C.chart (γ t)‖^2 ≤ 1/2)
    (hunit : ∀ t ∈ Icc a b, g.inner (γ t) (v t) (v t) = 1) :
    ∃ (l : ℝ) (w c : Space n), (b-a)/3 ≤ l ∧ l ≤ 4*(b-a) ∧ ‖w‖ = 1 ∧
      C.chart '' (γ '' Icc a b) = OAI.MeasureTheory.Kakeya.unitSegment (l • w) c := by
  have hg := hc.map_beltrami (κ := κ) (Φ := C.chart)
    (fun t ht => C.positive _ (hinside ht))
    (fun t ht => ((C.smooth _ (hinside ht)).contDiffAt
      (C.chart.open_source.mem_nhds (hinside ht))).of_le (by simp))
    (by
      intro t ht
      filter_upwards [C.chart.open_source.mem_nhds (hinside ht)] with y hy
      exact C.metric y hy)
  have hu : ∀ t ∈ Icc a b, beltramiMetric κ (C.chart (γ t))
      (fderiv ℝ (C.chart : Space n → Space n) (γ t) (v t))
      (fderiv ℝ (C.chart : Space n → Space n) (γ t) (v t)) = 1 := by
    intro t ht
    rw [← C.metric _ (hinside (hsub ht))]
    exact hunit t ht
  obtain ⟨he,hl,hh⟩ := hg.unitSpeed_segment_bounds hI hconn hab.le hsub hsmall hu
  have hne : C.chart (γ a) ≠ C.chart (γ b) := by
    intro hz
    rw [hz,dist_self] at hl
    linarith
  obtain ⟨w,c,hw,hrep⟩ := segment_eq_scaled_unitSegment hne
  refine ⟨dist (C.chart (γ a)) (C.chart (γ b)),w,c,hl,hh,hw,?_⟩
  rw [← image_comp]
  exact he.trans hrep

end LocalBeltramiChart
end OAI.Geometry.Nikodym
