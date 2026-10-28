import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ChartCoordinates

/-! # Coordinate One Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CoordinateOneForms

noncomputable section

/-! # Actual local holomorphic one-forms in the original quotient

Holomorphic coefficient functions multiply the differentials of genuine chart
coordinates. Their original chart evaluation is the usual coordinate sum.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "ModelI" => 𝓘(ℂ, E)

/-- The actual Kähler one-form with holomorphic coefficients in a genuine chart. -/
def originalCoordinateOneForm (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (extChartAt ModelI z).source)
    (a : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) :
    Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) 1 :=
  ∑ j, Algebra.DeRham.Basic.mk ℂ _ 1 (a j) (fun _ => ChartCoordinates.originalChartCoordinate X U z hU j)

/-- Original evaluation gives exactly the coefficient times coordinate-covector formula. -/
theorem chartEvaluation_originalCoordinateOneForm
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (extChartAt ModelI z).source)
    (a : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U))
    {y : E} (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z)
    (v : Fin 1 → E) :
    ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z 1
        (originalCoordinateOneForm X U z hU a) y v =
      ∑ j, (a j).1 ⟨(extChartAt ModelI z).symm y, hy.2⟩ * v 0 j := by
  simp only [originalCoordinateOneForm, map_sum, Finset.sum_apply,
    ContinuousAlternatingMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ z 1 _ _ hy]
  simp only [ComplexPoint.Basic.ComplexSchemePoint.chartGeneratorEvaluation, ContinuousAlternatingMap.smul_apply,
    ComplexPoint.Basic.ComplexSchemePoint.chartSection_apply_of_mem X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) _ z _ hy,
    ChartCoordinates.chartSectionDifferential_originalChartCoordinate X U z hU j hy,
    Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_apply_eq_det, Matrix.det_fin_one,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CoordinateOneForms
