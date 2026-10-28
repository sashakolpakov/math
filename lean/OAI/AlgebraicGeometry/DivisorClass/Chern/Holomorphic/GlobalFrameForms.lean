import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.Frames
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative

/-! # Global Frame Forms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalFrameForms

noncomputable section

/-! The literal frame coefficients of original global bundle forms, without a metric multiplier. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  (u : Connecting.holomorphicUnitCohomology E M) (i : M) (n : ℕ)

def holomorphicLineGlobalFrame : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n →ₗ[ℂ]
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (CohomologyTransitions.holomorphicCohomologyDomain E M u i) n where
  toFun a := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (le_inf le_top le_rfl) (a.val i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem holomorphicLineGlobalFrame_apply (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicLineGlobalFrame u i n a x = a.val i ⟨x.val, trivial, x.property⟩ := rfl

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem holomorphicLineGlobalFrame_inChart (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (e : OpenPartialHomeomorph M E) {y : E} (hy : e.symm y ∈ CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    (holomorphicLineGlobalFrame u i n a).extension.inChart e y = (a.val i).extension.inChart e y :=
  Open.ManifoldBidegree.openManifold_restrict_inChart (le_inf le_top le_rfl) (a.val i) e hy

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalFrameForms
