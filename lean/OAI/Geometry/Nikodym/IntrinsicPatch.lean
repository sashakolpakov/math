import OAI.Geometry.Nikodym.IntrinsicChartLipschitz
import OAI.Geometry.Nikodym.Chart.SmallNeighborhood

noncomputable section
namespace OAI.Geometry.Nikodym.LocalBeltramiChart

open Set _root_.MeasureTheory Metric
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}
variable (C : LocalBeltramiChart g κ x₀)

def intrinsicPatch (V : Set E) : Set (IntrinsicDomain g) :=
  C.intrinsicSource ∩ C.intrinsicForward ⁻¹' V

omit [FiniteDimensional ℝ E] in
theorem measurableSet_intrinsicPatch {V : Set E} (hV : MeasurableSet V) :
    MeasurableSet (C.intrinsicPatch V) :=
  C.isOpen_intrinsicSource.measurableSet.inter (C.measurable_intrinsicForward hV)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem intrinsicInverse_image {V : Set E} (hV : V ⊆ C.chart.target) :
    C.intrinsicInverse '' V = C.intrinsicPatch V := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨C.intrinsicInverse_mem (hV hy),by
      simpa only [mem_preimage,C.intrinsicForward_inverse (hV hy)] using hy⟩
  · rintro ⟨hx,hv⟩
    exact ⟨C.intrinsicForward x,hv,C.intrinsicInverse_forward hx⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem coordinate_patch_subset {V : Set E} (_ : V ⊆ C.chart.target) :
    C.intrinsicPatch V ⊆ OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g ⁻¹' (C.chart.symm '' V) := by
  rintro x ⟨hx,hv⟩
  refine ⟨C.intrinsicForward x,hv,?_⟩
  rw [C.intrinsicForward_eq hx]
  exact C.chart.left_inv hx

omit [MeasurableSpace E] [BorelSpace E] in
/-- Quantitative intrinsic chart geometry on one fixed local patch.
The hypotheses are the coordinate lower/upper Lipschitz bounds already
derived from ellipticity and actual Riemannian path length. -/
theorem exists_intrinsic_controlled_patch {A B : NNReal}
    (ha : LipschitzWith A (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g))
    (hb : LipschitzWith B (OAI.Geometry.Nikodym.IntrinsicDomain.ofCoordinate g)) :
    ∃ (r : ℝ) (K L : NNReal), 0 < r ∧ 1 ≤ K ∧ 1 ≤ L ∧
      closedBall (0 : E) (2*r) ⊆ C.chart.target ∧
      (∀ x ∈ closedBall (0 : E) (2*r), |κ| * ‖x‖^2 ≤ 1/2) ∧
      LipschitzOnWith K C.intrinsicForward (C.intrinsicPatch (ball 0 (2*r))) ∧
      LipschitzOnWith L C.intrinsicInverse (closedBall 0 (2*r)) ∧
      IsCompact (C.intrinsicPatch (closedBall 0 r)) := by
  obtain ⟨r,K,L,hr,hK,hL,ht,hsmall,hf,hi,hcompact,hs⟩ := C.exists_small_biLipschitz_target_ball
  have hp : C.chart.symm '' closedBall (0 : E) (2*r) ⊆ C.chart.source := hs
  have hFi := C.intrinsicForward_lipschitz ha hp hf
  have hIi := C.intrinsicInverse_lipschitz hb ht hi
  have hinc : C.intrinsicPatch (ball 0 (2*r)) ⊆
      OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g ⁻¹' (C.chart.symm '' closedBall (0 : E) (2*r)) := by
    intro x hx
    have hh := C.coordinate_patch_subset (ball_subset_closedBall.trans ht) hx
    exact (image_mono ball_subset_closedBall) hh
  have hcore : closedBall (0 : E) r ⊆ closedBall 0 (2*r) :=
    closedBall_subset_closedBall (by linarith)
  refine ⟨r,max (K*A) 1,max (B*L) 1,hr,le_max_right _ _,le_max_right _ _,ht,hsmall,
    (hFi.mono hinc).weaken (le_max_left _ _),hIi.weaken (le_max_left _ _),?_⟩
  rw [← C.intrinsicInverse_image (hcore.trans ht)]
  exact (isCompact_closedBall (0 : E) r).image_of_continuousOn
    ((hIi.mono hcore).continuousOn)

end OAI.Geometry.Nikodym.LocalBeltramiChart
