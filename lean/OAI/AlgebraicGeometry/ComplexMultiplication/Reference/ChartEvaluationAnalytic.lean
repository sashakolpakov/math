import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CotangentEvaluation
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Chart Evaluation Analytic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ChartEvaluationAnalytic

noncomputable section

/-! # Analytic chart values of the unchanged holomorphic-form quotient -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set A} {r : ℕ∞ω}

/-- Wedges of analytic covector fields are analytic. -/
theorem contDiffOn_wedgeCovectors (p : ℕ)
    (L : Fin p → A → V →L[ℂ] ℂ) (hL : ∀ i, ContDiffOn ℂ r (L i) s) :
    ContDiffOn ℂ r (fun x => OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors ℂ V
      (fun i => L i x)) s := by
  induction p with
  | zero =>
      simpa only [OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_zero] using
        (contDiffOn_const : ContDiffOn ℂ r
          (fun _ : A => ContinuousAlternatingMap.constOfIsEmpty ℂ V (Fin 0) (1 : ℂ)) s)
  | succ p ih =>
      have htail := ih (fun i => L i.succ) (fun i => hL i.succ)
      have hprod := (hL 0).smulRight htail
      have h := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ V ℂ :
        (V →L[ℂ] V [⋀^Fin p]→L[ℂ] ℂ) →L[ℂ] V [⋀^Fin (p + 1)]→L[ℂ] ℂ).contDiff.comp_contDiffOn hprod
      apply h.congr
      intro x _
      rw [Function.comp_apply, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
      exact OAI.Analysis.Foundations.NormedSpaceWedgeCovectors.ContinuousAlternatingMap.wedgeCovectors_succ p (fun i => L i x)

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- Every chart evaluation of an original Kähler form is analytic on its actual domain. -/
theorem contDiffOn_originalChartEvaluation
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X) (p : ℕ)
    (θ : Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) p) :
    ContDiffOn ℂ ω (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p θ)
      (ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z) := by
  induction θ using Algebra.DeRham.Basic.mk_induction with
  | mk a₀ v =>
      have ha := ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffOn X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z a₀
      have hd (i : Fin p) :=
        (ComplexPoint.Basic.ComplexSchemePoint.chartSection_contDiffOn X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z (v i)).fderivWithin
          (ComplexPoint.Basic.ComplexSchemePoint.isOpen_chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z).uniqueDiffOn
          (m := ω) (by simp)
      have h := ha.smul (contDiffOn_wedgeCovectors p
        (fun i => ComplexPoint.Basic.ComplexSchemePoint.chartSectionDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z (v i)) hd)
      apply h.congr
      intro y hy
      exact ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_mk X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p a₀ v hy
  | zero =>
      apply (contDiffOn_const (c := (0 : (Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ) [⋀^Fin p]→L[ℂ] ℂ))).congr
      intro y _
      exact congrFun (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_zero X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p) y
  | add a b ha hb =>
      apply (ha.add hb).congr
      intro y _
      exact congrFun (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_add X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p a b) y
  | smul c a ha =>
      apply (ha.const_smul c).congr
      intro y _
      exact congrFun (ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation_smul X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z p c a) y

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ChartEvaluationAnalytic
