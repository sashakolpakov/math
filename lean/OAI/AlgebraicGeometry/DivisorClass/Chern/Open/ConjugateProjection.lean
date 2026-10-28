import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConjugateForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.OneFormProjection

/-! # Conjugate Projection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConjugateProjection

noncomputable section

/-! Conjugation exchanges the actual holomorphic and antiholomorphic one-form projections. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M} {n : ℕ}

theorem openManifoldConjugate_zero : ConjugateForms.openManifoldConjugate (0 : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [ConjugateForms.openManifoldConjugate_apply]
  exact map_zero _

theorem openManifoldConjugate_add (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    ConjugateForms.openManifoldConjugate (a + b) = ConjugateForms.openManifoldConjugate a + ConjugateForms.openManifoldConjugate b := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply, ContinuousAlternatingMap.add_apply,
    ConjugateForms.openManifoldConjugate_apply, ConjugateForms.openManifoldConjugate_apply, ConjugateForms.openManifoldConjugate_apply,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply, ContinuousAlternatingMap.add_apply, map_add]

theorem openManifoldConjugate_smul (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    ConjugateForms.openManifoldConjugate (c • a) = conj c • ConjugateForms.openManifoldConjugate a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smul_apply, ContinuousAlternatingMap.smul_apply,
    ConjugateForms.openManifoldConjugate_apply, ConjugateForms.openManifoldConjugate_apply,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smul_apply, ContinuousAlternatingMap.smul_apply]
  exact map_mul _ c (a x v)

theorem openManifoldConjugate_action (z : ℂˣ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    ConjugateForms.openManifoldConjugate (ManifoldAction.openManifoldComplexAction z a) = ManifoldAction.openManifoldComplexAction z (ConjugateForms.openManifoldConjugate a) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [ConjugateForms.openManifoldConjugate_apply, ManifoldAction.openManifoldComplexAction_apply, ManifoldAction.openManifoldComplexAction_apply]
  exact (ConjugateForms.openManifoldConjugate_apply a x _).symm

theorem openManifoldConjugate_onePart (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    ConjugateForms.openManifoldConjugate (Manifold.OneFormProjection.openManifoldOnePart c a) = Manifold.OneFormProjection.openManifoldOnePart (conj c) (ConjugateForms.openManifoldConjugate a) := by
  change ConjugateForms.openManifoldConjugate ((1 / 2 : ℂ) • (a + c • ManifoldAction.openManifoldComplexAction AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit⁻¹ a)) = _
  rw [openManifoldConjugate_smul, openManifoldConjugate_add, openManifoldConjugate_smul,
    openManifoldConjugate_action]
  have hc : conj (1 / 2 : ℂ) = 1 / 2 := by
    apply Complex.ext
    · rfl
    · change -(1 / 2 : ℂ).im = (1 / 2 : ℂ).im
      norm_num [Complex.div_im]
  rw [hc]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConjugateProjection
