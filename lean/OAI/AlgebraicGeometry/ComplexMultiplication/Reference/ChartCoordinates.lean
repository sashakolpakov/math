import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CotangentEvaluation
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Chart Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ChartCoordinates

noncomputable section

/-! # Coordinate functions in the unchanged original holomorphic algebra

On an open contained in an actual chart source, the genuine coordinate
functions are holomorphic and their coordinate differentials are the standard
complex coordinate covectors.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "ModelI" => 𝓘(ℂ, E)

/-- A genuine chart coordinate as a section of the original holomorphic-function algebra. -/
def originalChartCoordinate (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (extChartAt ModelI z).source)
    (j : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) : ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) := by
  refine ⟨fun x => extChartAt ModelI z x.val j, ?_⟩
  have hp : ContMDiff ModelI 𝓘(ℂ, ℂ) ω (fun y : E => y j) :=
    (contDiff_apply ℂ ℂ j).contMDiff
  exact hp.comp
    ((contMDiffOn_extChartAt (I := ModelI) (x := z) (n := ω)).comp_contMDiff contMDiff_subtype_val
      (fun x => by simpa only [extChartAt_source] using hU x.property))

/-- The original section has precisely its actual coordinate value. -/
theorem originalChartCoordinate_apply (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (extChartAt ModelI z).source)
    (j : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) (x : U) :
    (originalChartCoordinate X U z hU j).1 x = extChartAt ModelI z x.val j := rfl

/-- The same chart expresses the genuine coordinate function as a standard coordinate. -/
theorem chartSection_originalChartCoordinate (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (extChartAt ModelI z).source)
    (j : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) {y : E}
    (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z) :
    ComplexPoint.Basic.ComplexSchemePoint.chartSection X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z
      (originalChartCoordinate X U z hU j) y = y j := by
  rw [ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ z _ hy]
  change extChartAt ModelI z ((extChartAt ModelI z).symm y) j = y j
  rw [(extChartAt ModelI z).right_inv hy.1]

/-- The actual coordinate derivative is the standard complex coordinate covector. -/
theorem chartSectionDifferential_originalChartCoordinate
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (extChartAt ModelI z).source)
    (j : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) {y : E}
    (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z) :
    ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z
      (originalChartCoordinate X U z hU j) y = ContinuousLinearMap.proj j := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential
  rw [fderivWithin_congr'
    (fun w hw => chartSection_originalChartCoordinate X U z hU j hw) hy]
  exact (ContinuousLinearMap.proj j : E →L[ℂ] ℂ).fderivWithin
    ((ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z).uniqueDiffWithinAt hy)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ChartCoordinates
