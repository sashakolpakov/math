import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RealFormSmooth
import OAI.AlgebraicGeometry.ComplexMultiplication.FormRestrictScalars
import OAI.Analysis.DifferentialForms.Manifold.LocalDerivative

/-! # Real Form Differential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RealFormDifferential

noncomputable section

/-! # The original exterior derivative on genuine real tangent forms

The original quotient differential agrees with the actual manifold exterior
derivative at every point of the original analytic open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Set Filter
open scoped ContDiff _root_.Manifold _root_.Topology

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)

/-- Exterior differentiation is retained in the actual original real chart. -/
theorem originalHolomorphicRealRawForm_differential_inChart
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) p)
    (z : ComplexPoint.Basic.ComplexSchemePoint X) {y : E}
    (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z) :
    (RealFormSmooth.originalHolomorphicRealRawForm X U p
      ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ θ)).exteriorDerivative.inChart
        (chartAt E z) y =
      (RealFormSmooth.originalHolomorphicRealRawForm X U (p + 1)
        ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) (p + 1)).mkQ
          (Algebra.DeRham.Basic.differential ℂ
            (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) p θ))).inChart
              (chartAt E z) y := by
  let form := RealFormSmooth.originalHolomorphicRealRawForm X U p
    ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ θ)
  let C := ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p θ
  let D := ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z
  have hopen : IsOpen D := ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z
  have hreal := RealFormSmooth.originalHolomorphicRealRawForm_smooth X U p
    ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ θ)
  have hlocal : form.inChart (chartAt E z) =ᶠ[𝓝 y] fun t => (C t).restrictScalars ℝ := by
    filter_upwards [hopen.mem_nhds hy] with t ht
    exact RealFormSmooth.originalHolomorphicRealRawForm_mk_inChart X U p θ z ht
  have hc : DifferentiableAt ℂ C y :=
    ((ChartEvaluationAnalytic.contDiffOn_originalChartEvaluation X U z p θ).contDiffAt
      (hopen.mem_nhds hy)).differentiableAt (by simp)
  have hchart := Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.exteriorDerivative_inChart_on form U.isOpen
    hreal (chartAt E z) (chart_mem_atlas E z)
    ((RealFormSmooth.originalChartSectionDomain_eq_realDomain X U z) ▸ hy)
  rw [hchart, hlocal.extDeriv_eq, FormRestrictScalars.extDeriv_restrictScalars C hc,
    RealFormSmooth.originalHolomorphicRealRawForm_mk_inChart X U (p + 1) _ z hy,
    ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_differential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p θ hy]
  congr 1
  unfold extDerivWithin extDeriv
  rw [fderivWithin_of_isOpen hopen hy]

/-- The original differential agrees pointwise with the actual manifold differential on U. -/
theorem originalHolomorphicRealRawForm_differential
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) (x : U) :
    (RealFormSmooth.originalHolomorphicRealRawForm X U p θ).exteriorDerivative x =
      RealFormSmooth.originalHolomorphicRealRawForm X U (p + 1)
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFormDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p θ) x := by
  obtain ⟨a, rfl⟩ := (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ_surjective θ
  let e := chartAt E x.val
  have hex : x.val ∈ e.source := mem_chart_source E x.val
  have he : e ∈ atlas E (ComplexPoint.Basic.ComplexSchemePoint X) := chart_mem_atlas E x.val
  have hy : e x.val ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) :=
    ⟨e.map_source hex, by
      change e.symm (e x.val) ∈ U
      simpa only [e.left_inv hex] using x.property⟩
  have hd := originalHolomorphicRealRawForm_differential_inChart X U p a x.val
    ((RealFormSmooth.originalChartSectionDomain_eq_realDomain X U x.val).symm ▸ hy)
  apply ContinuousAlternatingMap.ext
  intro v
  let T := Analysis.DifferentialForms.Manifold.TangentCoordinates.chartTangentEquiv e he x.val hex
  have hv := congrArg (fun c : E [⋀^Fin (p + 1)]→L[ℝ] ℂ => c (fun i => T (v i))) hd
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ e he x.val hex,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_at _ e he x.val hex] at hv
  have htuple : (fun i => T.symm (T (v i))) = v := funext fun i => T.symm_apply_apply (v i)
  rw [htuple] at hv
  exact hv

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RealFormDifferential
