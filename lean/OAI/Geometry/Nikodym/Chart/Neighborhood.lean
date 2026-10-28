import OAI.Geometry.Nikodym.SpaceFormChart
import OAI.Geometry.Nikodym.Chart.Segments

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter Metric
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace LocalBeltramiChart

variable {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}
variable (C : LocalBeltramiChart g κ x₀)

omit [FiniteDimensional ℝ E] in
theorem center_mem_target : (0 : E) ∈ C.chart.target := by
  simpa only [C.base_value] using C.chart.map_source C.base_mem

omit [FiniteDimensional ℝ E] in
theorem inverse_center : C.chart.symm (0 : E) = x₀ := by
  simpa only [C.base_value] using C.chart.left_inv C.base_mem

/-- A fixed smaller compact chart region has uniform Lipschitz constants
in both directions and a full surrounding target ball. -/
theorem exists_biLipschitz_target_ball :
    ∃ (r : ℝ) (K L : NNReal), 0 < r ∧ 1 ≤ K ∧ 1 ≤ L ∧
      closedBall (0 : E) (2*r) ⊆ C.chart.target ∧
      LipschitzOnWith K (C.chart : E → E)
        (C.chart.symm '' closedBall (0 : E) (2*r)) ∧
      LipschitzOnWith L (C.chart.symm : E → E) (closedBall (0 : E) (2*r)) ∧
      IsCompact (C.chart.symm '' closedBall (0 : E) (2*r)) ∧
      C.chart.symm '' closedBall (0 : E) (2*r) ⊆ C.chart.source := by
  have hc := (C.smooth x₀ C.base_mem).contDiffAt (C.chart.open_source.mem_nhds C.base_mem)
  have hi := (C.inverse_smooth 0 C.center_mem_target).contDiffAt
    (C.chart.open_target.mem_nhds C.center_mem_target)
  obtain ⟨K,U,hU,hK⟩ := (hc.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
  obtain ⟨L,V,hV,hL⟩ := (hi.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
  have hpre : C.chart.symm ⁻¹' U ∈ 𝓝 (0 : E) := by
    apply hi.continuousAt.preimage_mem_nhds
    simpa only [C.inverse_center] using hU
  have hgood : C.chart.target ∩ V ∩ C.chart.symm ⁻¹' U ∈ 𝓝 (0 : E) :=
    inter_mem (inter_mem (C.chart.open_target.mem_nhds C.center_mem_target) hV) hpre
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let r := s/4
  have hr : 0 < r := div_pos hs (by norm_num)
  have hb : closedBall (0 : E) (2*r) ⊆ ball 0 s :=
    closedBall_subset_ball (by dsimp [r]; linarith)
  have ht : closedBall (0 : E) (2*r) ⊆ C.chart.target := fun x hx => (hball (hb hx)).1.1
  have hv : closedBall (0 : E) (2*r) ⊆ V := fun x hx => (hball (hb hx)).1.2
  have hu : C.chart.symm '' closedBall (0 : E) (2*r) ⊆ U := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hball (hb hx)).2
  refine ⟨r,max K 1,max L 1,hr,le_max_right _ _,le_max_right _ _,ht,?_,?_,?_,?_⟩
  · exact (hK.mono hu).weaken (le_max_left _ _)
  · exact (hL.mono hv).weaken (le_max_left _ _)
  · exact (isCompact_closedBall (0 : E) (2*r)).image_of_continuousOn
      (C.inverse_smooth.continuousOn.mono ht)
  · rintro _ ⟨x,hx,rfl⟩
    exact C.chart.map_target (ht hx)

end LocalBeltramiChart

/-- The surrounding chart ball gives a uniform tubular margin for every
segment contained in its half-radius compact core. -/
theorem tube_subset_double_ball {n : ℕ} {r δ : ℝ} {v a : Space n}
    (hδ : δ ≤ r) (hseg : OAI.MeasureTheory.Kakeya.unitSegment v a ⊆ closedBall 0 r) :
    OAI.MeasureTheory.Kakeya.tube δ v a ⊆ ball 0 (2*r) := by
  intro x hx
  obtain ⟨t,ht,hxt⟩ := OAI.MeasureTheory.Kakeya.mem_tube_iff.mp hx
  have hy := hseg ⟨t,ht,rfl⟩
  rw [mem_closedBall] at hy
  rw [mem_ball]
  calc
    dist x 0 ≤ dist x (a+t•v) + dist (a+t•v) 0 := dist_triangle _ _ _
    _ < δ + r := add_lt_add_of_lt_of_le hxt hy
    _ ≤ 2*r := by linarith

end OAI.Geometry.Nikodym
