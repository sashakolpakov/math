import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantLocal
import OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicAbelianRealGroup
import OAI.AlgebraicGeometry.ComplexMultiplication.InvariantPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.OpenForms

/-! # Abelian Invariant Smooth -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantSmooth

noncomputable section

/-! # Original local holomorphic representatives of actual invariant smooth one-forms -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" =>
  (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)

/-- The actual native invariant form transported by the proved analytic identity. -/
def originalAbelianInvariantSmoothForm (α : N →L[ℂ] ℂ) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E (ComplexPoint.Basic.ComplexSchemePoint X) 1 :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm
    (IntrinsicAbelianRealGroup.originalToNativeAbelianPoint_realSmooth X)
    (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (InvariantPullback.complexInvariantIdentityCovector (G := AnalyticIntrinsicAtlasRegular.NativePointManifold X) α))

/-- The original quotient form has exactly the full actual smooth tangent values on its domain. -/
theorem originalAbelianInvariantOneForm_smooth
    (α : N →L[ℂ] ℂ) (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    (z : ComplexPoint.Basic.ComplexSchemePoint X) (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (chartAt E z).source) :
    ReferenceSmooth.OpenForms.originalHolomorphicToSmoothOpenForm X U 1
      ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) 1).mkQ
        (AbelianInvariantLocal.originalAbelianInvariantOneForm X α U z hU)) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (originalAbelianInvariantSmoothForm X α) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  let c := chartAt E z
  have hc : c ∈ atlas E (ComplexPoint.Basic.ComplexSchemePoint X) := chart_mem_atlas E z
  have hx : x.val ∈ c.source := hU x.property
  have hy : c x.val ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z := by
    refine ⟨?_, ?_⟩
    · simpa only [extChartAt_target, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Set.preimage_id, Set.range_id, Set.inter_univ]
        using c.map_source hx
    · change c.symm (c x.val) ∈ U
      rw [c.left_inv hx]
      exact x.property
  have hchart : (RealFormSmooth.originalHolomorphicRealRawForm X U 1
      ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) 1).mkQ
        (AbelianInvariantLocal.originalAbelianInvariantOneForm X α U z hU))).inChart c (c x.val) =
      (originalAbelianInvariantSmoothForm X α : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E (ComplexPoint.Basic.ComplexSchemePoint X) 1).inChart
        c (c x.val) := by
    rw [RealFormSmooth.originalHolomorphicRealRawForm_mk_inChart X U 1 _ z hy]
    apply ContinuousAlternatingMap.ext
    intro w
    change ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z 1
      (AbelianInvariantLocal.originalAbelianInvariantOneForm X α U z hU) (c x.val) w = _
    rw [AbelianInvariantLocal.chartEvaluation_originalAbelianInvariantOneForm X α U z hU hy]
    exact (InvariantPullback.complexInvariantRawForm_pullback_inChart α
      (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm
      (IntrinsicAbelianAnalyticGroup.originalToNativeAbelianPoint_analytic X) c hc (c.map_source hx) w).symm
  let e := Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv c hc x.val hx
  have hv := congrArg (fun a : E [⋀^Fin 1]→L[ℝ] ℂ => a (fun i => e (v i))) hchart
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ c hc x.val hx,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ c hc x.val hx] at hv
  have htuple : (fun i : Fin 1 => e.symm (e (v i))) = v :=
    funext fun i => e.symm_apply_apply (v i)
  change RealFormSmooth.originalHolomorphicRealRawForm X U 1
      ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) 1).mkQ
        (AbelianInvariantLocal.originalAbelianInvariantOneForm X α U z hU)) x.val
        (fun i => e.symm (e (v i))) =
    (originalAbelianInvariantSmoothForm X α : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E (ComplexPoint.Basic.ComplexSchemePoint X) 1)
      x.val (fun i => e.symm (e (v i))) at hv
  rw [htuple] at hv
  exact hv

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantSmooth
