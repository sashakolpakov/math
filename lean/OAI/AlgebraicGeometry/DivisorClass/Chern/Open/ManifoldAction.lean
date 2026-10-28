import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.Analysis.DifferentialForms.Manifold.ChartEquiv

/-! # Manifold Action -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldAction

noncomputable section

/-! The original complex tangent action on actual open manifold forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {n : ℕ} {U V : Opens M}

def openManifoldComplexAction (z : ℂˣ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n where
  toFun form := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ofRaw U
    (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z form.extension) (form.smooth.complexAction z)
  map_add' f g := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    change Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z (f + g).extension x = _
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, map_add]
    rfl
  map_smul' c f := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    change Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z (c • f).extension x = _
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_smul, map_smul]
    rfl

theorem openManifoldComplexAction_apply (z : ℂˣ)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (x : U) :
    openManifoldComplexAction z form x = (form x).compContinuousLinearMap
      (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap (x : M) (↑(z⁻¹) : ℂ)) := by
  change (form.extension x).compContinuousLinearMap _ = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply]

theorem openManifoldComplexAction_restrict (z : ℂˣ) (h : V ≤ U)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (openManifoldComplexAction z form) =
      openManifoldComplexAction z (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h form) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply, openManifoldComplexAction_apply]

theorem openManifoldComplexAction_inChart (z : ℂˣ)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) :
    (openManifoldComplexAction z form).extension.inChart e y =
      (form.extension.inChart e y).compContinuousLinearMap
        (ContinuousLinearMap.lsmul ℝ ℂ (↑(z⁻¹) : ℂ)) := by
  have h : (openManifoldComplexAction z form).extension.inChart e y =
      (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z form.extension).inChart e y := by
    unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply
      (openManifoldComplexAction z form) ⟨e.symm y, hy.2⟩]
    rfl
  exact h.trans (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart z form.extension e he hy.1)

theorem openManifoldComplexAction_onOpen (z : ℂˣ) (U : Opens M)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    openManifoldComplexAction z (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U form) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction z form) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [openManifoldComplexAction_apply]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldAction
