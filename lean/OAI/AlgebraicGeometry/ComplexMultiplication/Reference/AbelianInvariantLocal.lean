import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InvariantCoefficientFunctions
import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicAbelianAnalyticGroup

/-! # Abelian Invariant Local -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantLocal

noncomputable section

/-! # Actual original local holomorphic forms on the original abelian scheme

The analytic identity and the target Lie group are proved from the original
scheme. Neither is supplied as an additional mathematical hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.CategoryTheory.MonObj

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)

/-- An actual original local holomorphic representative from a native complex covector. -/
def originalAbelianInvariantOneForm (α : N →L[ℂ] ℂ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (chartAt E z).source) :
    Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) 1 :=
  InvariantCoefficientFunctions.originalInvariantOneForm X (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm
    (IntrinsicAbelianAnalyticGroup.originalToNativeAbelianPoint_analytic X) α U z hU
    (chartAt N (1 : AnalyticIntrinsicAtlasRegular.NativePointManifold X)) (chart_mem_atlas N _)
    (mem_chart_source N _)

/-- Its full original chart value is the derivative of the actual native group operation. -/
theorem chartEvaluation_originalAbelianInvariantOneForm (α : N →L[ℂ] ℂ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (chartAt E z).source)
    {y : E} (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z)
    (v : Fin 1 → E) :
    ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z 1
        (originalAbelianInvariantOneForm X α U z hU) y v =
      (α.comp (fderiv ℂ (fun w =>
        (chartAt N (1 : AnalyticIntrinsicAtlasRegular.NativePointManifold X))
          (((AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm ((chartAt E z).symm y))⁻¹ *
            (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm ((chartAt E z).symm w))) y)) (v 0) :=
  InvariantCoefficientFunctions.chartEvaluation_originalInvariantOneForm X (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm
    (IntrinsicAbelianAnalyticGroup.originalToNativeAbelianPoint_analytic X) α U z hU
    (chartAt N (1 : AnalyticIntrinsicAtlasRegular.NativePointManifold X)) (chart_mem_atlas N _)
    (mem_chart_source N _) hy v

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantLocal
