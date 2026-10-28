import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantSmooth
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Local

/-! # Abelian Invariant Global -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantGlobal

noncomputable section

/-! # Global original holomorphic representatives of actual invariant one-forms

Local representatives are constructed in actual original chart domains. Their
proved smooth values agree on overlaps, and faithfulness of the original
holomorphic sheaf map gives a unique gluing. No local or global lift is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)

/-- Every actual invariant complex covector has a unique global original holomorphic section. -/
theorem originalAbelianInvariantGlobal_existsUnique (α : N →L[ℂ] ℂ) :
    ∃! θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).presheaf.obj (op ⊤),
      ReferenceSmooth.Local.originalHolomorphicToSmoothSheafSection X 1 ⊤ θ =
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (AbelianInvariantSmooth.originalAbelianInvariantSmoothForm X α) := by
  apply ReferenceSmooth.Local.originalHolomorphicSheaf_existsUnique_of_local_forms X 1 ⊤
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (AbelianInvariantSmooth.originalAbelianInvariantSmoothForm X α))
  intro x
  let V : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
    ⟨(chartAt E x.val).source, (chartAt E x.val).open_source⟩
  have hV : (V : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (chartAt E x.val).source := Set.Subset.rfl
  refine ⟨V, le_top, mem_chart_source E x.val,
    (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (op V) 1).mkQ
      (AbelianInvariantLocal.originalAbelianInvariantOneForm X α V x.val hV), ?_⟩
  rw [AbelianInvariantSmooth.originalAbelianInvariantOneForm_smooth X α V x.val hV,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen]

/-- The actual unique original section, with its values proved by the construction. -/
def originalAbelianInvariantGlobalSection (α : N →L[ℂ] ℂ) :
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) 1).presheaf.obj (op ⊤) :=
  (originalAbelianInvariantGlobal_existsUnique X α).exists.choose

/-- Its full global smooth form is the pullback of the actual native invariant form. -/
theorem originalAbelianInvariantGlobalSection_smooth (α : N →L[ℂ] ℂ) :
    ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm X 1
      (originalAbelianInvariantGlobalSection X α) = AbelianInvariantSmooth.originalAbelianInvariantSmoothForm X α := by
  have h := (originalAbelianInvariantGlobal_existsUnique X α).exists.choose_spec
  change ReferenceSmooth.Local.originalHolomorphicToSmoothSheafSection X 1 ⊤
    (originalAbelianInvariantGlobalSection X α) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (AbelianInvariantSmooth.originalAbelianInvariantSmoothForm X α) at h
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  have he := congrArg (fun f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens (ComplexPoint.Basic.ComplexSchemePoint X)) 1 =>
    f ⟨x, by simp⟩) h
  exact (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply
    (ReferenceSmooth.Local.originalHolomorphicToSmoothSheafSection X 1 ⊤
      (originalAbelianInvariantGlobalSection X α)) x).trans he

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantGlobal
