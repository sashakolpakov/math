import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientCriterion
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DeRhamComplex

/-! # Chart Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartCoefficients

noncomputable section

/-! BettiComparison's actual holomorphic forms have exactly complex-differentiable coordinate coefficients. -/

open Filter
open scoped _root_.Manifold ContDiff _root_.Topology

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n : ℕ}

theorem pureManifold_coefficients_criterion (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M n 0)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a.val).val.inChart e y) ↔
      DifferentiableAt ℂ (a.val.val.inChart e) y := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart a.val e he hy]
  apply CoefficientCriterion.pureForm_extDeriv_pure_iff
  · exact (Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart a.val.smooth e he hy).differentiableAt (by simp)
  · filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact a.hasBidegree_inChart e he hz

theorem mem_forms_iff_coefficients_complex (a : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M n 0) :
    a ∈ DeRhamComplex.forms E M n ↔ ∀ e ∈ atlas E M, ∀ y ∈ e.target,
      DifferentiableAt ℂ (a.val.val.inChart e) y := by
  rw [DeRhamComplex.mem_forms_iff_derivative_pure]
  constructor
  · intro h e he y hy
    exact (pureManifold_coefficients_criterion a e he hy).mp (h e he y hy)
  · intro h e he y hy
    exact (pureManifold_coefficients_criterion a e he hy).mpr (h e he y hy)

theorem form_coefficients_complex (a : DeRhamComplex.forms E M n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    DifferentiableAt ℂ ((DeRhamComplex.inclusion E M n a).val.inChart e) y :=
  (mem_forms_iff_coefficients_complex a.val).mp a.property e he y hy

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartCoefficients
