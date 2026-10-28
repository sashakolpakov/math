import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.Dolbeault
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantDolbeaultCompatibility

/-! # Anti Multiplication -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiMultiplication

noncomputable section

/-! Actual smooth scalar multiplication preserves bundle antiholomorphic forms and commutes with the original one-form projection. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  (u : Connecting.holomorphicUnitCohomology E M) (U : Opens M)
  (f : M → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f)

theorem holomorphicLineSmoothMul_inChart (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : M)
    (e : OpenPartialHomeomorph M E) {y : E}
    (hy : e.symm y ∈ U ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    ((SupportedForms.holomorphicLineSmoothMul u U n f hf a).val i).extension.inChart e y =
      f (e.symm y) • (a.val i).extension.inChart e y := by
  unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩,
    SupportedForms.holomorphicLineSmoothMul_apply]
  ext v
  rfl

theorem holomorphicLineSmoothMul_anti (q : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u U q) :
    SupportedForms.holomorphicLineSmoothMul u U q f hf a.val ∈ HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u U q := by
  intro i e he y hy c v
  rw [holomorphicLineSmoothMul_inChart u U f hf q a.val i e hy.2]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [a.property i e he y hy c v]
  ring

theorem holomorphicLineOnePart_smoothMul (c : ℂ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) :
    OneFormProjection.holomorphicLineOnePart u U c (SupportedForms.holomorphicLineSmoothMul u U 1 f hf a) =
      SupportedForms.holomorphicLineSmoothMul u U 1 f hf (OneFormProjection.holomorphicLineOnePart u U c a) := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  change Manifold.OneFormProjection.openManifoldOnePart c ((SupportedForms.holomorphicLineSmoothMul u U 1 f hf a).val i) x = _
  rw [OneFormProjection.openManifoldOnePart_apply, SupportedForms.holomorphicLineSmoothMul_apply, SupportedForms.holomorphicLineSmoothMul_apply]
  change (1 / 2 : ℂ) • (f x • a.val i x + c • (f x • a.val i x).compContinuousLinearMap
    (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap x.val Complex.I)) = f x • Manifold.OneFormProjection.openManifoldOnePart c (a.val i) x
  rw [OneFormProjection.openManifoldOnePart_apply]
  ext v
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, smul_eq_mul]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiMultiplication
