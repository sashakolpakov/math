import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOpenConnection

/-! # Real Scalar Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarCurvature

noncomputable section

/-! Curvature of a real metric potential is imaginary-valued, proved with the actual conjugation operator. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M}

theorem smoothScalarOpenCurvature_add_conjugate (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hf : ∀ x : U, conj (f x) = f x) :
    ScalarOpenConnection.smoothScalarOpenCurvature f + Open.ConjugateForms.openManifoldConjugate (ScalarOpenConnection.smoothScalarOpenCurvature f) = 0 := by
  have hF : Open.ConjugateForms.openManifoldConjugate (SmoothScalarForm.smoothScalarOpenZeroForm f) = SmoothScalarForm.smoothScalarOpenZeroForm f := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    ext v
    rw [Open.ConjugateForms.openManifoldConjugate_apply, SmoothScalarForm.smoothScalarOpenZeroForm_apply]
    exact hf x
  have hdF : Open.ConjugateForms.openManifoldConjugate (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f) := by
    rw [← Open.ConjugateForms.openManifoldConjugate_d, hF]
  have hI : conj (-Complex.I) = Complex.I := by
    apply Complex.ext <;> norm_num
  have hc : Open.ConjugateForms.openManifoldConjugate (ScalarOpenConnection.smoothScalarOpenCurvature f) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart Complex.I (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f))) := by
    rw [ScalarOpenConnection.smoothScalarOpenCurvature, ← Open.ConjugateForms.openManifoldConjugate_d, Open.ConjugateProjection.openManifoldConjugate_onePart, hI, hdF]
  rw [hc]
  have h := congrArg Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d
    (Manifold.OneFormProjection.openManifoldOnePart_add (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)))
  rw [map_add, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared] at h
  exact h

theorem smoothScalarOpenCurvature_re_zero (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hf : ∀ x : U, conj (f x) = f x) (x : U) (v : Fin 2 → TangentSpace 𝓘(ℝ, E) x.val) :
    (ScalarOpenConnection.smoothScalarOpenCurvature f x v).re = 0 := by
  have h := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2 => (a x v).re)
    (smoothScalarOpenCurvature_add_conjugate f hf)
  simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply, ContinuousAlternatingMap.add_apply,
    Open.ConjugateForms.openManifoldConjugate_apply, Complex.add_re, Complex.conj_re] at h
  change (ScalarOpenConnection.smoothScalarOpenCurvature f x v).re + (ScalarOpenConnection.smoothScalarOpenCurvature f x v).re = 0 at h
  linarith

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarCurvature
