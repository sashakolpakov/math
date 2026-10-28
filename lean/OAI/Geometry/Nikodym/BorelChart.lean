import Mathlib

noncomputable section
namespace OAI.Geometry.Nikodym

open Set

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

/-- Canonical total measurable extension of a local chart. No regularity
of the arbitrary values of a partial homeomorphism outside its source is used. -/
def borelChartForward (H : OpenPartialHomeomorph M N) (b : N) : M → N := by
  classical
  exact H.source.piecewise H (fun _ => b)

def borelChartInverse (H : OpenPartialHomeomorph M N) (a : M) : N → M :=
  borelChartForward H.symm a

omit [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N] in
theorem borelChartForward_eq (H : OpenPartialHomeomorph M N) (b : N)
    {x : M} (hx : x ∈ H.source) : borelChartForward H b x = H x := by
  classical
  exact piecewise_eq_of_mem _ _ _ hx

omit [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N] in
theorem borelChartInverse_eq (H : OpenPartialHomeomorph M N) (a : M)
    {y : N} (hy : y ∈ H.target) : borelChartInverse H a y = H.symm y :=
  borelChartForward_eq H.symm a hy

theorem measurable_borelChartForward (H : OpenPartialHomeomorph M N) (b : N) :
    Measurable (borelChartForward H b) := by
  classical
  exact H.continuousOn.measurable_piecewise continuousOn_const H.open_source.measurableSet

theorem measurable_borelChartInverse (H : OpenPartialHomeomorph M N) (a : M) :
    Measurable (borelChartInverse H a) := measurable_borelChartForward H.symm a

omit [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N] in
theorem borelChartInverse_forward (H : OpenPartialHomeomorph M N) (a : M) (b : N)
    {x : M} (hx : x ∈ H.source) :
    borelChartInverse H a (borelChartForward H b x) = x := by
  rw [borelChartForward_eq H b hx,borelChartInverse_eq H a (H.map_source hx)]
  exact H.left_inv hx

omit [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N] in
theorem borelChartForward_inverse (H : OpenPartialHomeomorph M N) (a : M) (b : N)
    {y : N} (hy : y ∈ H.target) :
    borelChartForward H b (borelChartInverse H a y) = y := by
  rw [borelChartInverse_eq H a hy,borelChartForward_eq H b (H.map_target hy)]
  exact H.right_inv hy

end OAI.Geometry.Nikodym
