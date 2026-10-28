import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarPotential

/-! # Global Scalar Conjugation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalScalarConjugation

noncomputable section

/-! Conjugation of the actual scalar curvature operator and real scalar potentials. -/

open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem conjugate_oneFormAntiholomorphicPart (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) :
    ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) = ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormHolomorphicPart (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm a) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change star ((1 / 2 : ℂ) * (a x v + Complex.I * _)) =
    (1 / 2 : ℂ) * (star (a x v) - Complex.I * star _)
  simp [sub_eq_add_neg]

theorem globalScalarCurvature_conjugate (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    Projective.ScalarPotential.globalScalarCurvature (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f) = -ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (Projective.ScalarPotential.globalScalarCurvature f) := by
  have hd := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneForm_parts_add (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f))
  rw [map_add, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared] at hd
  have he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormAntiholomorphicPart (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)) =
      -Projective.ScalarPotential.globalScalarCurvature f := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hd)
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormHolomorphicPart (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f))) = _
  rw [ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm, ← conjugate_oneFormAntiholomorphicPart, ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.d_conjugateSmoothForm]
  exact (congrArg ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm he).trans (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothFormMap.map_neg (Projective.ScalarPotential.globalScalarCurvature f))

def realScalarPotentialPart (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 :=
  (1 / 2 : ℂ) • (f + ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem realScalarPotentialPart_conjugate (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (realScalarPotentialPart f) = realScalarPotentialPart f := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change star ((1 / 2 : ℂ) * (f x v + star (f x v))) = (1 / 2 : ℂ) * (f x v + star (f x v))
  simp [add_comm]

theorem globalScalarCurvature_realPart (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (hf : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (Projective.ScalarPotential.globalScalarCurvature f) = -Projective.ScalarPotential.globalScalarCurvature f) :
    Projective.ScalarPotential.globalScalarCurvature (realScalarPotentialPart f) = Projective.ScalarPotential.globalScalarCurvature f := by
  unfold realScalarPotentialPart
  rw [map_smul, map_add, globalScalarCurvature_conjugate, hf, neg_neg]
  module

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalScalarConjugation
