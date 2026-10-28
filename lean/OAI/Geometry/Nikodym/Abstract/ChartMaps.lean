import OAI.Geometry.Nikodym.Abstract.Chart
import OAI.Geometry.Nikodym.AtlasMaps

noncomputable section
open Set _root_.MeasureTheory Manifold Bundle
open scoped ContDiff

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=E) p) κ
  (extChartAt 𝓘(ℝ,E) p p))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldChart_source_subset_ext :
    C.manifoldChart.source ⊆ (extChartAt 𝓘(ℝ,E) p).source := by
  rw [extChartAt_source]
  exact C.manifoldChart_source_subset

def manifoldForward : M → E := by
  classical
  exact C.manifoldChart.source.piecewise C.manifoldChart (fun _ => 0)

def manifoldInverse : E → M := by
  classical
  exact C.manifoldChart.target.piecewise C.manifoldChart.symm (fun _ => p)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldForward_eq {x : M} (hx : x ∈ C.manifoldChart.source) :
    C.manifoldForward x = C.manifoldChart x := by
  classical
  exact piecewise_eq_of_mem _ _ _ hx

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldInverse_eq {y : E} (hy : y ∈ C.chart.target) :
    C.manifoldInverse y = C.manifoldChart.symm y := by
  classical
  exact piecewise_eq_of_mem _ _ _ (C.manifoldChart_target.symm ▸ hy)

theorem measurable_manifoldForward : Measurable C.manifoldForward := by
  classical
  exact C.manifoldChart.continuousOn.measurable_piecewise continuousOn_const
    C.manifoldChart.open_source.measurableSet

theorem measurable_manifoldInverse : Measurable C.manifoldInverse := by
  classical
  exact C.manifoldChart.symm.continuousOn.measurable_piecewise continuousOn_const
    C.manifoldChart.open_target.measurableSet

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldForward_mem {x : M} (hx : x ∈ C.manifoldChart.source) :
    C.manifoldForward x ∈ C.chart.target := by
  rw [C.manifoldForward_eq hx,←C.manifoldChart_target]
  exact C.manifoldChart.map_source hx

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldInverse_mem {y : E} (hy : y ∈ C.chart.target) :
    C.manifoldInverse y ∈ C.manifoldChart.source := by
  rw [C.manifoldInverse_eq hy]
  exact C.manifoldChart.map_target (C.manifoldChart_target.symm ▸ hy)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldInverse_forward {x : M} (hx : x ∈ C.manifoldChart.source) :
    C.manifoldInverse (C.manifoldForward x) = x := by
  rw [C.manifoldInverse_eq (C.manifoldForward_mem hx),C.manifoldForward_eq hx]
  exact C.manifoldChart.left_inv hx

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldForward_inverse {y : E} (hy : y ∈ C.chart.target) :
    C.manifoldForward (C.manifoldInverse y) = y := by
  rw [C.manifoldForward_eq (C.manifoldInverse_mem hy),C.manifoldInverse_eq hy]
  exact C.manifoldChart.right_inv (C.manifoldChart_target.symm ▸ hy)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldForward_eq_chart_atlasForward {x : M}
    (hx : x ∈ C.manifoldChart.source) :
    C.manifoldForward x = C.chart (atlasForward (E:=E) p x) := by
  rw [C.manifoldForward_eq hx,C.manifoldChart_apply,atlasForward_eq p]
  exact C.manifoldChart_source_subset_ext hx

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem atlasForward_mem_chart_source {x : M} (hx : x ∈ C.manifoldChart.source) :
    atlasForward (E:=E) p x ∈ C.chart.source := by
  rw [atlasForward_eq p (C.manifoldChart_source_subset_ext hx)]
  exact hx.2

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldForward_image_eq {A : Set M} (hA : A ⊆ C.manifoldChart.source) :
    C.manifoldForward '' A = C.chart '' (atlasForward (E:=E) p '' A) := by
  rw [image_image]
  apply image_congr
  intro x hx
  exact C.manifoldForward_eq_chart_atlasForward (hA hx)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldForward_image_eq_preimage {A : Set M} (hA : A ⊆ C.manifoldChart.source) :
    C.manifoldForward '' A = C.chart.target ∩ C.manifoldInverse ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨C.manifoldForward_mem (hA hx),by
      simpa only [mem_preimage,C.manifoldInverse_forward (hA hx)] using hx⟩
  · rintro ⟨hy,hx⟩
    exact ⟨C.manifoldInverse y,hx,C.manifoldForward_inverse hy⟩

theorem measurableSet_manifoldForward_image {A : Set M}
    (hAm : MeasurableSet A) (hA : A ⊆ C.manifoldChart.source) :
    MeasurableSet (C.manifoldForward '' A) := by
  rw [C.manifoldForward_image_eq_preimage hA]
  exact C.chart.open_target.measurableSet.inter (C.measurable_manifoldInverse hAm)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem manifoldForward_image_patch {V : Set E} (hV : V ⊆ C.chart.target) :
    C.manifoldForward '' (C.manifoldChart.source ∩ C.manifoldForward ⁻¹' V) = V := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx.2
  · intro hy
    exact ⟨C.manifoldInverse y,⟨C.manifoldInverse_mem (hV hy),by
      simpa only [mem_preimage,C.manifoldForward_inverse (hV hy)] using hy⟩,
      C.manifoldForward_inverse (hV hy)⟩

end OAI.Geometry.Nikodym.LocalBeltramiChart
