import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedDerivativeProjection

/-! # One Form Mixed Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormMixedDerivative

noncomputable section

/-! The exterior derivative of the holomorphic part of a closed one-form has actual type (1,1). -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U : Opens M}

theorem openManifoldOnePart_holomorphic_d_mixed_of_closed (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (ha : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) a)) := by
  have hb := MixedDerivativeProjection.openManifoldOnePart_dbar_zero_of_closed a ha
  have hdA : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart Complex.I a) =
      Open.ManifoldDolbeault.openManifoldDolbeaultPrime 0 1 1 (Manifold.OneFormProjection.openManifoldOnePart Complex.I a) := by
    rw [← Open.ManifoldDolbeault.openManifoldDolbeaultPrime_add_dbar 0 1, hb, add_zero]
  have hs := congrArg Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart_add a)
  rw [map_add, ha, hdA] at hs
  have he : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) a) =
      (-1 : ℂ) • Open.ManifoldDolbeault.openManifoldDolbeaultPrime 0 1 1 (Manifold.OneFormProjection.openManifoldOnePart Complex.I a) := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    ext v
    have hsx := congrArg (fun f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2 => f x v) hs
    change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) a) x v +
      Open.ManifoldDolbeault.openManifoldDolbeaultPrime 0 1 1 (Manifold.OneFormProjection.openManifoldOnePart Complex.I a) x v = 0 at hsx
    change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) a) x v =
      (-1 : ℂ) * Open.ManifoldDolbeault.openManifoldDolbeaultPrime 0 1 1 (Manifold.OneFormProjection.openManifoldOnePart Complex.I a) x v
    linear_combination hsx
  rw [he]
  exact Open.ManifoldDolbeault.openManifoldHasBidegree_smul (-1)
    (Open.ManifoldDolbeault.openManifoldDolbeaultPrime_hasBidegree rfl (Manifold.OneFormProjection.openManifoldOnePart_antiholomorphic a))

theorem openManifold_d_holomorphic_d_mixed (f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d f))) :=
  openManifoldOnePart_holomorphic_d_mixed_of_closed (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d f)
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared f)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormMixedDerivative
