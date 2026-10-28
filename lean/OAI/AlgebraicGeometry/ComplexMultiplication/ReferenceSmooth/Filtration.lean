import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Local
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation

/-! # Filtration -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Filtration

noncomputable section

/-! # Original holomorphic forms retain their actual smooth Hodge filtration -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X

/-- Extending an actual holomorphic sheaf section by zero retains its tangent type. -/
theorem originalHolomorphicSmoothSection_extension_pure (p : ℕ) (U : Opens (TopCat.of M))
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (op U)) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M p 0
      (Local.originalHolomorphicToSmoothSheafSection X p U θ).extension := by
  intro x z v
  by_cases hx : x ∈ U
  · rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨x, hx⟩]
    exact Local.originalHolomorphicToSmoothSheaf_pure X p U θ ⟨x, hx⟩ z v
  · simp [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension,
      Analysis.DifferentialForms.Manifold.Open.openManifoldFormExtension, hx]

/-- Every original holomorphic section has genuine pure type on its original open domain. -/
theorem originalHolomorphicSmoothSection_open_pure (p : ℕ) (U : Opens (TopCat.of M))
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (op U)) :
    DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p 0
      (Local.originalHolomorphicToSmoothSheafSection X p U θ) := by
  have h := (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mpr
    (originalHolomorphicSmoothSection_extension_pure X p U θ)
  intro e he y hy
  exact h e he y hy.1

/-- Thus the unchanged original section lies in every allowed smooth filtration step. -/
theorem originalHolomorphicSmoothSection_filtered (p : ℕ) (U : Opens (TopCat.of M))
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (op U))
    (r : ℤ) (hr : r ≤ (p : ℤ)) :
    Local.originalHolomorphicToSmoothSheafSection X p U θ ∈
      Comparison.Betti.Open.FiltrationDescent.Hodge.openFormFiltration U p r := by
  let i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree p := ⟨(p, 0), by simp⟩
  apply Comparison.Betti.Open.ChartEvaluation.Hodge.openPureFormsInDegree_mem_filtration U p i r hr
  exact (Comparison.Betti.Open.ChartEvaluation.Hodge.mem_openPureFormsInDegree_iff U p i _).mpr
    (originalHolomorphicSmoothSection_open_pure X p U θ)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.Filtration
