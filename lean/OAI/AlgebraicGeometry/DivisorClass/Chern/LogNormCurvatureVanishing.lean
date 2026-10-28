import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOpenConnection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ExponentialEpi

/-! # Log Norm Curvature Vanishing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LogNormCurvatureVanishing

noncomputable section

/-! The logarithm of the squared norm of an actual holomorphic unit has zero local curvature. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M}

theorem smoothScalarOpenCurvature_logNormSq_unit
    (g : (Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))ˣ) (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hf : ∀ x : U, f x = (Real.log (Complex.normSq (g.val x)) : ℂ)) :
    ScalarOpenConnection.smoothScalarOpenCurvature f = 0 := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  obtain ⟨V, hVU, hxV, l, hl⟩ := Holomorphic.ExponentialEpi.exists_holomorphicSubopenLog g x
  have hv : ScalarOpenConnection.smoothScalarOpenCurvature (SmoothScalarForm.smoothComplexOpenFunctionRestrict hVU f) = 0 :=
    ScalarOpenConnection.smoothScalarOpenCurvature_logNormSq_exp l (SmoothScalarForm.smoothComplexOpenFunctionRestrict hVU f) (by
      intro y
      change f ⟨y.val, hVU y.property⟩ = _
      rw [hf, hl y])
  have hr : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hVU (ScalarOpenConnection.smoothScalarOpenCurvature f) = 0 :=
    (ScalarOpenConnection.smoothScalarOpenCurvature_restrict hVU f).trans hv
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V 2 => a ⟨x.val, hxV⟩ v) hr

theorem smoothScalarOpenCurvature_eq_of_logNormSq_difference
    (g : (Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))ˣ)
    (f h : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hf : ∀ x : U, (f - h) x = (Real.log (Complex.normSq (g.val x)) : ℂ)) :
    ScalarOpenConnection.smoothScalarOpenCurvature f = ScalarOpenConnection.smoothScalarOpenCurvature h := by
  have hz := smoothScalarOpenCurvature_logNormSq_unit g (f - h) hf
  have he : f = (f - h) + h := (sub_add_cancel f h).symm
  conv_lhs => rw [he]
  rw [ScalarOpenConnection.smoothScalarOpenCurvature_add, hz, zero_add]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LogNormCurvatureVanishing
