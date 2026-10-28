import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ChartEvaluationAnalytic
import OAI.AlgebraicGeometry.ComplexMultiplication.CovectorRealForm
import OAI.AlgebraicGeometry.ComplexMultiplication.ChartInverseTangent
import OAI.Analysis.DifferentialForms.Manifold.Transition

/-! # Real Form Smooth -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RealFormSmooth

noncomputable section

section

/-! # Actual chart expressions of original holomorphic forms on real tangents

On the actual analytic open, the real tangent form has exactly the restriction
of the original complex chart evaluation as its chart expression.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "I" => 𝓘(ℂ, E)

/-- The original preferred complex cotangent values, supported on the actual open. -/
def originalHolomorphicOriginalComplexField
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) :
    ComplexPoint.Basic.ComplexSchemePoint X → E [⋀^Fin p]→L[ℂ] ℂ := by
  classical
  exact fun x => if hx : x ∈ U then
    CotangentEvaluation.originalHolomorphicCotangentEvaluation X U p θ ⟨x, hx⟩ else 0

/-- Actual real tangent covectors for an original holomorphic-form class. -/
def originalHolomorphicRealRawForm
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E (ComplexPoint.Basic.ComplexSchemePoint X) p :=
  CovectorRealForm.complexCovectorFieldToRealForm p (originalHolomorphicOriginalComplexField X U p θ)

/-- At a domain point, the actual field has the original quotient evaluation. -/
theorem originalHolomorphicOriginalComplexField_mk_apply
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) p)
    (x : U) :
    originalHolomorphicOriginalComplexField X U p
      ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ θ) x =
      CotangentEvaluation.originalKahlerCotangentEvaluation X U p θ x := by
  exact dite_eq_left x.property

/-- The original identity chart map is the genuine chart transition. -/
theorem originalSchemeChartMap_identity (z t : ComplexPoint.Basic.ComplexSchemePoint X) :
    HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z t = (chartAt E t) ∘ (chartAt E z).symm := by
  funext w
  change (extChartAt I t) (ComplexPoint.Basic.Point.map (𝟙 X) ((extChartAt I z).symm w)) = _
  rw [ComplexPoint.Basic.Point.map_id]
  rfl

/-- The chart transition is expressed through the actual real tangent maps. -/
theorem originalRealChartTangentTransition (z t x : ComplexPoint.Basic.ComplexSchemePoint X)
    (hz : x ∈ (chartAt E z).source) (ht : x ∈ (chartAt E t).source) :
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (chartAt E t) x).comp
      (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap (chartAt E z) ((chartAt E z) x)) =
      (fderiv ℂ ((chartAt E t) ∘ (chartAt E z).symm)
        ((chartAt E z) x)).restrictScalars ℝ :=
  Analysis.DifferentialForms.Manifold.ComplexAction.chartTransition_tangent_eq_complex (chartAt E z) (chartAt E t)
    (chart_mem_atlas E z) (chart_mem_atlas E t) x hz ht

/-- At an inverse-chart point, the original scheme identity has the same tangent map. -/
theorem originalIdentityChartTangentTransition (z : ComplexPoint.Basic.ComplexSchemePoint X) {y : E}
    (hy : y ∈ (chartAt E z).target) :
    (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (chartAt E ((chartAt E z).symm y))
      ((chartAt E z).symm y)).comp (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap (chartAt E z) y) =
      (fderiv ℂ (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z ((chartAt E z).symm y)) y).restrictScalars ℝ := by
  rw [originalSchemeChartMap_identity]
  exact ChartInverseTangent.chartTransition_tangent_eq_complex_at_inverse (chartAt E z)
    (chartAt E ((chartAt E z).symm y)) (chart_mem_atlas E z)
    (chart_mem_atlas E ((chartAt E z).symm y)) hy
    (mem_chart_source E ((chartAt E z).symm y))

/-- The complete real chart expression equals the unchanged original complex expression. -/
theorem originalHolomorphicRealRawForm_mk_inChart
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) p)
    (z : ComplexPoint.Basic.ComplexSchemePoint X) {y : E}
    (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z) :
    (originalHolomorphicRealRawForm X U p
      ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ θ)).inChart
        (chartAt E z) y =
      (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p θ y).restrictScalars ℝ := by
  classical
  let e := chartAt E z
  let x := e.symm y
  let f := chartAt E x
  have hyt : y ∈ e.target := hy.1.2
  have hx : x ∈ U := hy.2
  have hd := originalIdentityChartTangentTransition X z hyt
  have hc := CotangentEvaluation.chartEvaluation_eq_cotangentEvaluation X U p θ z hy
  have hfield := originalHolomorphicOriginalComplexField_mk_apply X U p θ ⟨x, hx⟩
  apply ContinuousAlternatingMap.ext
  intro v
  change (originalHolomorphicOriginalComplexField X U p
      ((ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ θ) x)
      (fun i => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f x
        (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e y (v i))) =
    (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p θ y) v
  rw [hfield]
  rw [hc]
  change (CotangentEvaluation.originalKahlerCotangentEvaluation X U p θ ⟨x, hx⟩)
      (fun i => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap f x
        (Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap e y (v i))) =
    (CotangentEvaluation.originalKahlerCotangentEvaluation X U p θ ⟨x, hx⟩)
      (fun i => fderiv ℂ (HolomorphicFormPullback.originalSchemeChartMap (𝟙 X) z x) y (v i))
  apply congrArg (CotangentEvaluation.originalKahlerCotangentEvaluation X U p θ ⟨x, hx⟩)
  funext i
  exact congrArg (fun g => g (v i)) hd

end

/-! # Original holomorphic forms are genuine smooth forms on their analytic opens

Only smoothness on the original open is asserted. No boundary regularity of
the zero extension is used.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)

/-- The two actual chart domains are the same subset of the original coordinate space. -/
theorem originalChartSectionDomain_eq_realDomain
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X) :
    ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z =
      Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain (chartAt E z) (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  simp [ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain, Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain]

/-- Original holomorphic-form classes have actual smooth real tangent values on U. -/
theorem originalHolomorphicRealRawForm_smooth
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (p : ℕ)
    (θ : ComplexPoint.Basic.ComplexSchemePoint.HolomorphicForm X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (originalHolomorphicRealRawForm X U p θ)
      (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) := by
  obtain ⟨a, rfl⟩ := (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluationKernel X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) p).mkQ_surjective θ
  intro e he
  obtain ⟨z, rfl⟩ := he
  have hc := ChartEvaluationAnalytic.contDiffOn_originalChartEvaluation X U z p a
  have hr := (hc.of_le (show (∞ : WithTop ℕ∞) ≤ ω from le_top)).restrict_scalars ℝ
  let R : (E [⋀^Fin p]→L[ℂ] ℂ) →L[ℝ] (E [⋀^Fin p]→L[ℝ] ℂ) :=
    (ContinuousAlternatingMap.restrictScalarsLI ℝ).toContinuousLinearMap
  have h := R.contDiff.comp_contDiffOn hr
  rw [originalChartSectionDomain_eq_realDomain] at h
  apply h.congr
  intro y hy
  exact originalHolomorphicRealRawForm_mk_inChart X U p a z
    ((originalChartSectionDomain_eq_realDomain X U z).symm ▸ hy)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RealFormSmooth
