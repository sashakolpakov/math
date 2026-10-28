import OAI.Geometry.Nikodym.Abstract.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section
open Set _root_.MeasureTheory Manifold

namespace OAI.Geometry.Nikodym

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]

/-- Ordinary atlas coordinates, measurably extended outside their source. -/
def atlasForward (p : M) : M → E := by
  classical
  exact (extChartAt 𝓘(ℝ,E) p).source.piecewise (extChartAt 𝓘(ℝ,E) p) (fun _ => 0)

/-- Inverse atlas coordinates, measurably extended by the chart center. -/
def atlasInverse (p : M) : E → M := by
  classical
  exact (extChartAt 𝓘(ℝ,E) p).target.piecewise
    (extChartAt 𝓘(ℝ,E) p).symm (fun _ => p)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem atlasForward_eq (p : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source) :
    atlasForward (E:=E) p x = extChartAt 𝓘(ℝ,E) p x := by
  classical
  exact piecewise_eq_of_mem _ _ _ hx

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem atlasInverse_eq (p : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    atlasInverse p y = (extChartAt 𝓘(ℝ,E) p).symm y := by
  classical
  exact piecewise_eq_of_mem _ _ _ hy

theorem measurable_atlasForward (p : M) : Measurable (atlasForward (E:=E) p) := by
  classical
  exact (continuousOn_extChartAt p).measurable_piecewise continuousOn_const
    (isOpen_extChartAt_source p).measurableSet

theorem measurable_atlasInverse (p : M) : Measurable (atlasInverse (E:=E) p) := by
  classical
  exact (continuousOn_extChartAt_symm p).measurable_piecewise continuousOn_const
    (isOpen_extChartAt_target p).measurableSet

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem atlasForward_mem (p : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source) :
    atlasForward (E:=E) p x ∈ (extChartAt 𝓘(ℝ,E) p).target := by
  rw [atlasForward_eq p hx]
  exact (extChartAt 𝓘(ℝ,E) p).map_source hx

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem atlasInverse_mem (p : M) (y : E) :
    atlasInverse p y ∈ (extChartAt 𝓘(ℝ,E) p).source := by
  classical
  by_cases hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target
  · rw [atlasInverse_eq p hy]
    exact (extChartAt 𝓘(ℝ,E) p).map_target hy
  · rw [atlasInverse,piecewise_eq_of_notMem _ _ _ hy]
    exact mem_extChartAt_source p

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem atlasInverse_forward (p : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source) :
    atlasInverse p (atlasForward (E:=E) p x) = x := by
  rw [atlasInverse_eq p (atlasForward_mem p hx),atlasForward_eq p hx]
  exact (extChartAt 𝓘(ℝ,E) p).left_inv hx

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem atlasForward_inverse (p : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    atlasForward (E:=E) p (atlasInverse p y) = y := by
  rw [atlasForward_eq p (atlasInverse_mem p y),atlasInverse_eq p hy]
  exact (extChartAt 𝓘(ℝ,E) p).right_inv hy

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M] in
theorem atlasForward_image_eq (p : M) {A : Set M}
    (hA : A ⊆ (extChartAt 𝓘(ℝ,E) p).source) :
    atlasForward (E:=E) p '' A =
      (extChartAt 𝓘(ℝ,E) p).target ∩ atlasInverse p ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨atlasForward_mem p (hA hx),by
      simpa only [mem_preimage,atlasInverse_forward p (hA hx)] using hx⟩
  · rintro ⟨hy,hx⟩
    exact ⟨atlasInverse p y,hx,atlasForward_inverse p hy⟩

theorem measurableSet_atlasForward_image (p : M) {A : Set M}
    (hAm : MeasurableSet A) (hA : A ⊆ (extChartAt 𝓘(ℝ,E) p).source) :
    MeasurableSet (atlasForward (E:=E) p '' A) := by
  rw [atlasForward_image_eq p hA]
  exact (isOpen_extChartAt_target p).measurableSet.inter (measurable_atlasInverse p hAm)

end OAI.Geometry.Nikodym
