import OAI.Geometry.Nikodym.AmbientBeltramiControl
import OAI.Geometry.Nikodym.Abstract.ChartMaps
import OAI.Geometry.Nikodym.AmbientTubeMargin

noncomputable section
open Set Bundle Manifold Metric
open scoped ContDiff

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [PseudoEMetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

def manifoldPatch (V : Set E) : Set M :=
  C.manifoldChart.source ∩ C.manifoldForward ⁻¹' V

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldPatch_eq (V : Set E) :
    C.manifoldPatch V = C.manifoldChart.source ∩ C.manifoldChart ⁻¹' V := by
  ext x
  constructor <;> rintro ⟨hx,hv⟩ <;> refine ⟨hx,?_⟩
  · simpa only [mem_preimage,C.manifoldForward_eq hx] using hv
  · simpa only [mem_preimage,C.manifoldForward_eq hx] using hv

omit [IsContinuousRiemannianBundle E fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] [IsRiemannianManifold 𝓘(ℝ, E) M] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem isOpen_manifoldPatch {V : Set E} (hV : IsOpen V) :
    IsOpen (C.manifoldPatch V) := by
  rw [C.manifoldPatch_eq]
  exact C.manifoldChart.isOpen_inter_preimage hV

omit [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M] in
omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldInverse_image {V : Set E} (hV : V ⊆ C.chart.target) :
    C.manifoldInverse '' V = C.manifoldPatch V := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨C.manifoldInverse_mem (hV hy),by
      simpa only [mem_preimage,C.manifoldForward_inverse (hV hy)] using hy⟩
  · rintro ⟨hx,hv⟩
    exact ⟨C.manifoldForward x,hv,C.manifoldInverse_forward hx⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] [IsContinuousRiemannianBundle E fun x : M ↦ TangentSpace 𝓘(ℝ, E) x] [IsRiemannianManifold 𝓘(ℝ, E) M] in
theorem manifoldPatch_mono {V W : Set E} (hVW : V ⊆ W) :
    C.manifoldPatch V ⊆ C.manifoldPatch W := by
  rintro x ⟨hx,hv⟩
  exact ⟨hx,hVW hv⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
/-- One actual ambient-distance chart, with measurable total maps, an open
outer patch, and a compact inner core. -/
theorem exists_manifold_controlled_patch :
    ∃ (r : ℝ) (K L : NNReal), 0 < r ∧ 1 ≤ K ∧ 1 ≤ L ∧
      closedBall (0 : E) (2*r) ⊆ C.chart.target ∧
      (∀ y ∈ closedBall (0 : E) (2*r), |κ| * ‖y‖^2 ≤ 1/2) ∧
      LipschitzOnWith K C.manifoldForward (C.manifoldPatch (ball 0 (2*r))) ∧
      LipschitzOnWith L C.manifoldInverse (closedBall 0 (2*r)) ∧
      IsCompact (C.manifoldPatch (closedBall 0 r)) ∧
      IsOpen (C.manifoldPatch (ball 0 (2*r))) ∧
      p ∈ C.manifoldPatch (ball 0 r) := by
  obtain ⟨r,K,L,hr,hK,hL,ht,hs,hf,hi,hcompact⟩ :=
    exists_ambientBeltrami_controlled_ball p C
  have hie : EqOn C.manifoldInverse (ambientBeltramiInverse p C)
      (closedBall (0 : E) (2*r)) := by
    intro y hy
    exact C.manifoldInverse_eq (ht hy)
  have himage : ambientBeltramiInverse p C '' closedBall (0 : E) (2*r) =
      C.manifoldPatch (closedBall 0 (2*r)) := by
    rw [← C.manifoldInverse_image ht]
    exact image_congr (fun y hy => (hie hy).symm)
  rw [himage] at hf
  have hf' : LipschitzOnWith K C.manifoldForward
      (C.manifoldPatch (ball 0 (2*r))) := by
    intro x hx y hy
    rw [C.manifoldForward_eq hx.1,C.manifoldForward_eq hy.1]
    exact hf (C.manifoldPatch_mono ball_subset_closedBall hx)
      (C.manifoldPatch_mono ball_subset_closedBall hy)
  have hi' : LipschitzOnWith L C.manifoldInverse (closedBall (0 : E) (2*r)) := by
    intro x hx y hy
    rw [hie hx,hie hy]
    exact hi hx hy
  have hcore : closedBall (0 : E) r ⊆ closedBall 0 (2*r) :=
    closedBall_subset_closedBall (by linarith)
  refine ⟨r,K,L,hr,hK,hL,ht,hs,hf',hi',?_,C.isOpen_manifoldPatch isOpen_ball,?_⟩
  · rw [← C.manifoldInverse_image (hcore.trans ht)]
    exact (isCompact_closedBall (0 : E) r).image_of_continuousOn
      ((hi'.mono hcore).continuousOn)
  · refine ⟨C.manifoldChart_base_mem,?_⟩
    rw [mem_preimage,C.manifoldForward_eq C.manifoldChart_base_mem,C.manifoldChart_base_value]
    exact mem_ball_self hr

end OAI.Geometry.Nikodym.LocalBeltramiChart
