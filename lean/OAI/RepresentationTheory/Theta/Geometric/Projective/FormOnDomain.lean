import OAI.RepresentationTheory.Theta.Geometric.Projective.PeriodTests
import OAI.RepresentationTheory.Theta.Geometric.SmoothPullbackFaithfulness

/-! # Form On Domain -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.FormOnDomain

noncomputable section

/-! Exact smooth pullback of algebraic forms to the period domain,
with linear chart evaluation and actual period tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Filter
open scoped _root_.Topology _root_.Manifold ContDiff

def projectiveFormOnDomain (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (c : Ω → X.analyticSpace)
    (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X.toOver →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm LinearTheta.BallCoordinates Ω 1 := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback c (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)).comp
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X.toOver)

def periodChartEvaluation (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (x : Ω) (u : LinearTheta.BallCoordinates) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm LinearTheta.BallCoordinates Ω 1 →ₗ[ℂ] ℂ where
  toFun form := form.val.inChart (chartAt LinearTheta.BallCoordinates x) x.val (fun _ => u)
  map_add' form other := congrArg (fun f => f x.val (fun _ => u))
    (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add form.val other.val (chartAt LinearTheta.BallCoordinates x))
  map_smul' z form := congrArg (fun f => f x.val (fun _ => u))
    (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul z form.val (chartAt LinearTheta.BallCoordinates x))

theorem projectiveFormOnDomain_periodTest (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (c : Ω → X.analyticSpace)
    (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c) (x : Ω) :
    ∃ p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ X.toOver,
      (∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, Period.TestDensity.periodEvaluationPoint x.val y ≫ p = c ⟨y, hy⟩) ∧
      ∀ (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X.toOver) (u : LinearTheta.BallCoordinates),
        periodChartEvaluation Ω x u (projectiveFormOnDomain Ω X c hc form) =
          DifferentialNaturality.formInPeriodCoordinates x.val p form u :=
  PeriodTests.exists_projectivePeriodTest Ω X c hc x

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.FormOnDomain
