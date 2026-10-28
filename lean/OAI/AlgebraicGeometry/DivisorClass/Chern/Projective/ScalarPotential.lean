import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalMixedDerivative
import OAI.RepresentationTheory.Theta.Geometric.AntiholomorphicClosedRepresentative

/-! # Scalar Potential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarPotential

noncomputable section

/-! The actual projective scalar correction supplies curvature potentials for mixed derivatives of type parts. -/

open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def globalScalarCurvature : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d.comp (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormHolomorphicPart.comp Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d)

theorem globalScalarCurvature_closed (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (globalScalarCurvature f) = 0 := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared _

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem globalScalarCurvature_dbar (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val = -globalScalarCurvature f := by
  have hd := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneForm_parts_add (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f))
  rw [map_add, RepresentationTheory.Theta.Geometric.AntiholomorphicClosedRepresentative.antiholomorphicPart_d_eq_dbar V f, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared] at hd
  exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hd)

theorem exists_antiholomorphic_mixed_potential
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V.analyticModel V.analyticSpace 1 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) = (-2 : ℂ) • globalScalarCurvature f := by
  obtain ⟨f, b, hb, he⟩ := RepresentationTheory.Theta.Geometric.AntiholomorphicClosedRepresentative.exists_closed_antiholomorphic_representative V
    (GlobalMixedDerivative.manifoldOneAntiPure a) (GlobalMixedDerivative.manifoldOneAntiPure_dbar_zero_of_mixed a ha)
  have hd := congrArg (fun t : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm V.analyticModel V.analyticSpace 0 1 =>
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d t.val) he
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a) =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (b.val + (2 : ℂ) • (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.zeroFormPure f)).val) at hd
  rw [map_add, map_smul, hb, zero_add, globalScalarCurvature_dbar V f, smul_neg, ← neg_smul] at hd
  exact ⟨f, hd⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ScalarPotential
