import OAI.RepresentationTheory.Theta.Geometric.Projective.FormOnDomain
import OAI.RepresentationTheory.Theta.Geometric.CanonicalUniqueness

/-! # Algebraic Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! An actual period uniformization faithfully detects algebraic forms
through their smooth pullbacks to the ball. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.periodUniformization_forms_injective (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover) :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    Function.Injective (Projective.FormOnDomain.projectiveFormOnDomain D.domain X cover hc) := by
  dsimp only
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  have hd (x : D.domain) : Function.Surjective
      (mfderiv 𝓘(ℝ, LinearTheta.BallCoordinates) 𝓘(ℝ, X.analyticModel) cover x) := by
    intro v
    obtain ⟨u, hu⟩ := (hcover.2.2.2.1 x).surjective v
    exact ⟨u, (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_apply_eq_complex
      (hc.of_le (by simp)).contMDiffAt u).trans hu⟩
  intro form other h
  exact AlgebraicGeometry.AbelianScheme.TateComparison.GlobalFormFaithfulness.globalSmoothForm_injective X.toOver
    (SmoothPullbackFaithfulness.smoothFormPullback_injective cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc) hcover.1 hd 1 h)

end

end OAI.RepresentationTheory.Theta.Geometric
