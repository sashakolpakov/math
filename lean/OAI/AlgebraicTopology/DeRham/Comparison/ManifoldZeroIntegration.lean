import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration
import OAI.AlgebraicTopology.DeRham.Comparison.ZeroIntegration
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf

/-! # Manifold Zero Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldZeroIntegration

noncomputable section

/-!
# Degree-zero normalization of actual manifold cube integration

The integral over the zero-dimensional parameter cube is the actual value of
the form at its image point. Consequently the genuine locally constant
inclusion, evaluated by integration, is the ordinary value of the section.
-/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The genuine pullback of a zero-form is composition of its scalar value. -/
theorem manifoldCubePullback_zero_apply {n : ℕ} (sigma : ManifoldCubeIntegration.SmoothManifoldCube E M n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (x : Fin n → ℝ) :
    ManifoldCubeIntegration.manifoldCubePullback sigma form x 0 = form (sigma.toFun x) 0 := by
  change form (sigma.toFun x) _ = form (sigma.toFun x) 0
  exact congrArg (form (sigma.toFun x)) (Subsingleton.elim _ _)

/-- Actual integration over a point is evaluation, with normalization one. -/
@[simp]
theorem manifoldCubeIntegration_zero (sigma : ManifoldCubeIntegration.SmoothManifoldCube E M 0)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    ManifoldCubeIntegration.manifoldCubeIntegration sigma form = form (sigma.toFun 0) 0 := by
  rw [ManifoldCubeIntegration.manifoldCubeIntegration_apply, ZeroIntegration.complexIntegrateForm_zero_cube]
  exact manifoldCubePullback_zero_apply sigma form 0

/-- The actual global locally constant zero-form integrates to its section value. -/
theorem manifoldCubeIntegration_locallyConstant (sigma : ManifoldCubeIntegration.SmoothManifoldCube E M 0)
    (f : LocallyConstant (⊤ : Opens M) ℂ) :
    ManifoldCubeIntegration.manifoldCubeIntegration sigma
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E ⊤ f)) =
      f ⟨sigma.toFun 0, by trivial⟩ := by
  rw [manifoldCubeIntegration_zero, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply,
    Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply]

/-- In particular the constant section integrates to its specified complex scalar. -/
theorem manifoldCubeIntegration_const (sigma : ManifoldCubeIntegration.SmoothManifoldCube E M 0) (c : ℂ) :
    ManifoldCubeIntegration.manifoldCubeIntegration sigma
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal
          (Analysis.DifferentialForms.Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E ⊤ (LocallyConstant.const _ c))) = c :=
  manifoldCubeIntegration_locallyConstant sigma (LocallyConstant.const _ c)

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldZeroIntegration
