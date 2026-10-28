import OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarOperator
import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalRealScalarForm

/-! # Scalar Curvature Zero -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarCurvatureZero

noncomputable section

/-! Original scalar curvature vanishes on an actual zero scalar germ. -/

open Filter Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem realScalarChern_curvature_zero (z : E) :
    extDeriv (fun y => RealScalarOperator.realScalarChernOperator E (fderiv ℝ (fun _ : E => (0 : ℝ)) y)) z = 0 := by
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
    (fderiv ℝ (fun y => RealScalarOperator.realScalarChernOperator E (fderiv ℝ (fun _ : E => (0 : ℝ)) y)) z) = 0
  have hd (y : E) : fderiv ℝ (fun _ : E => (0 : ℝ)) y = 0 := (hasFDerivAt_const (0 : ℝ) y).fderiv
  have heq : (fun y => RealScalarOperator.realScalarChernOperator E (fderiv ℝ (fun _ : E => (0 : ℝ)) y)) =
      (fun _ : E => (0 : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1)) := by
    funext y
    exact (congrArg (RealScalarOperator.realScalarChernOperator E) (hd y)).trans (map_zero _)
  rw [heq, (hasFDerivAt_const (0 : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) z).fderiv, map_zero]

end

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem globalScalarCurvature_zero_onOpen (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (U : Opens M)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U f = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (Projective.ScalarPotential.globalScalarCurvature f) = 0 := by
  rw [← ScalarPotentialFunctions.scalarPotentialOpenFunction_curvature f U, ScalarOpenConnection.smoothScalarOpenCurvature,
    ScalarPotentialFunctions.scalarPotentialOpenFunction_zeroForm, hf]
  simp only [map_zero]

theorem globalRealScalarForm_curvature_zero_of_germ (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    {x : M} (hx : f =ᶠ[𝓝 x] 0) : Projective.ScalarPotential.globalScalarCurvature (GlobalRealScalarForm.globalRealScalarForm f hf) x = 0 := by
  obtain ⟨S, hS, hSo, hxS⟩ := mem_nhds_iff.mp hx
  let U : Opens M := ⟨S, hSo⟩
  have hzero : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (GlobalRealScalarForm.globalRealScalarForm f hf) = 0 := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro y
    ext v
    change GlobalRealScalarForm.globalRealScalarForm f hf y.val v = 0
    rw [GlobalRealScalarForm.globalRealScalarForm_apply, hS y.property]
    rfl
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2 => a ⟨x, hxS⟩)
    (globalScalarCurvature_zero_onOpen _ U hzero)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarCurvatureZero
