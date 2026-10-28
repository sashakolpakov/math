import OAI.Geometry.Nikodym.IntrinsicVolume
import OAI.Geometry.Nikodym.Chart.Neighborhood

noncomputable section
namespace OAI.Geometry.Nikodym.LocalBeltramiChart

open Set _root_.MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}
variable (C : LocalBeltramiChart g κ x₀)

def intrinsicSource : Set (IntrinsicDomain g) :=
  OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g ⁻¹' C.chart.source

def intrinsicForward (x : IntrinsicDomain g) : E := by
  classical
  exact C.chart.source.piecewise C.chart (fun _ => 0) (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g x)

def intrinsicInverse (y : E) : IntrinsicDomain g := by
  classical
  exact if hy : y ∈ C.chart.target then
    OAI.Geometry.Nikodym.IntrinsicDomain.ofCoordinate g ⟨C.chart.symm y,C.source_domain (C.chart.map_target hy)⟩
  else OAI.Geometry.Nikodym.IntrinsicDomain.ofCoordinate g ⟨x₀,C.source_domain C.base_mem⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem intrinsicForward_eq {x : IntrinsicDomain g} (hx : x ∈ C.intrinsicSource) :
    C.intrinsicForward x = C.chart (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g x) := by
  classical
  exact piecewise_eq_of_mem _ _ _ hx

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem coordinate_intrinsicInverse {y : E} (hy : y ∈ C.chart.target) :
    OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g (C.intrinsicInverse y) = C.chart.symm y := by
  classical
  simp [LocalBeltramiChart.intrinsicInverse,hy,OAI.Geometry.Nikodym.IntrinsicDomain.coordinate_ofCoordinate]

omit [FiniteDimensional ℝ E] in
theorem measurable_intrinsicForward : Measurable C.intrinsicForward := by
  classical
  exact (C.chart.continuousOn.measurable_piecewise continuousOn_const
    C.chart.open_source.measurableSet).comp (OAI.Geometry.Nikodym.IntrinsicDomain.measurableEmbedding_coordinate g).measurable

omit [FiniteDimensional ℝ E] in
theorem measurable_intrinsicInverse : Measurable C.intrinsicInverse := by
  classical
  apply (OAI.Geometry.Nikodym.IntrinsicDomain.measurableEmbedding_coordinate g).measurable_comp_iff.mp
  have he : OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g ∘ C.intrinsicInverse =
      C.chart.target.piecewise C.chart.symm (fun _ => x₀) := by
    ext y
    by_cases hy : y ∈ C.chart.target
    · simp [LocalBeltramiChart.intrinsicInverse,hy,OAI.Geometry.Nikodym.IntrinsicDomain.coordinate_ofCoordinate]
    · simp [LocalBeltramiChart.intrinsicInverse,hy,OAI.Geometry.Nikodym.IntrinsicDomain.coordinate_ofCoordinate]
  rw [he]
  exact C.chart.symm.continuousOn.measurable_piecewise continuousOn_const
    C.chart.open_target.measurableSet

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem isOpen_intrinsicSource : IsOpen C.intrinsicSource :=
  C.chart.open_source.preimage (OAI.Geometry.Nikodym.IntrinsicDomain.contMDiff_coordinate g).continuous

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem intrinsicForward_mem {x : IntrinsicDomain g} (hx : x ∈ C.intrinsicSource) :
    C.intrinsicForward x ∈ C.chart.target := by
  rw [C.intrinsicForward_eq hx]
  exact C.chart.map_source hx

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem intrinsicInverse_mem {y : E} (hy : y ∈ C.chart.target) :
    C.intrinsicInverse y ∈ C.intrinsicSource := by
  change OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g (C.intrinsicInverse y) ∈ C.chart.source
  rw [C.coordinate_intrinsicInverse hy]
  exact C.chart.map_target hy

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem intrinsicInverse_forward {x : IntrinsicDomain g} (hx : x ∈ C.intrinsicSource) :
    C.intrinsicInverse (C.intrinsicForward x) = x := by
  apply OAI.Geometry.Nikodym.IntrinsicDomain.coordinate_injective g
  rw [C.coordinate_intrinsicInverse (C.intrinsicForward_mem hx),C.intrinsicForward_eq hx]
  exact C.chart.left_inv hx

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem intrinsicForward_inverse {y : E} (hy : y ∈ C.chart.target) :
    C.intrinsicForward (C.intrinsicInverse y) = y := by
  rw [C.intrinsicForward_eq (C.intrinsicInverse_mem hy),C.coordinate_intrinsicInverse hy]
  exact C.chart.right_inv hy

end OAI.Geometry.Nikodym.LocalBeltramiChart
