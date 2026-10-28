import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence

/-! # Conjugate Forms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConjugateForms

noncomputable section

/-! Pointwise conjugation of actual open manifold forms through the native intrinsic equivalence. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {U : Opens M} {n : ℕ}

def openManifoldConjugate (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n :=
  (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a))

theorem openManifoldConjugate_apply (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (x : U)
    (v : Fin n → TangentSpace 𝓘(ℝ, E) x.val) : openManifoldConjugate a x v = conj (a x v) := by
  change conj (a x (fun i => (Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent.intrinsicOpenTangentEquiv (E := E) x)
    ((Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent.intrinsicOpenTangentEquiv (E := E) x).symm (v i)))) = conj (a x v)
  simp only [ContinuousLinearEquiv.apply_symm_apply]

theorem openManifoldConjugate_d (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (openManifoldConjugate a) = openManifoldConjugate (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a) := by
  unfold openManifoldConjugate
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_symm_d, ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm, Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d]

theorem openManifoldConjugate_involutive (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    openManifoldConjugate (openManifoldConjugate a) = a := by
  unfold openManifoldConjugate
  rw [LinearEquiv.apply_symm_apply, ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm_involutive, LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConjugateForms
