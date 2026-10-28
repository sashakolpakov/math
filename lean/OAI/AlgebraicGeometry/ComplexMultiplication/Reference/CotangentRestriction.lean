import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CotangentEvaluation

/-! # Cotangent Restriction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CotangentRestriction

noncomputable section

/-! # Actual cotangent evaluation commutes with original open restriction -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "I" => 𝓘(ℂ, E)

/-- Restriction retains the actual tangent covector at every point of the smaller open. -/
theorem originalHolomorphicCotangentEvaluation_restrict
    {U V : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))} (h : V ≤ U) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) (x : V) :
    CotangentEvaluation.originalHolomorphicCotangentEvaluation X V p
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormRestriction X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (homOfLE h).op p θ) x =
        CotangentEvaluation.originalHolomorphicCotangentEvaluation X U p θ ⟨x.val, h x.property⟩ := by
  obtain ⟨a, rfl⟩ := (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ_surjective θ
  have hy : extChartAt I x.val x.val ∈
      ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op V) x.val := by
    refine ⟨mem_extChartAt_target x.val, ?_⟩
    change (extChartAt I x.val).symm (extChartAt I x.val x.val) ∈ V
    rw [(extChartAt I x.val).left_inv (mem_extChartAt_source x.val)]
    exact x.property
  exact ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_formRestriction X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (homOfLE h).op x.val p a hy

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CotangentRestriction
