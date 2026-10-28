import OAI.RepresentationTheory.Theta.Geometric.Projective.FormOnDomain

/-! # Domain Precomposition -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.DomainPrecomposition

noncomputable section

/-! Precomposition of a period map agrees with pullback of the actual
smooth realization of its algebraic forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem projectiveFormOnDomain_precomp
    (Ω U : TopologicalSpace.Opens LinearTheta.BallCoordinates) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (c : U → X.analyticSpace) (r : Ω → U)
    (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c)
    (hr : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) ∞ r)
    (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X.toOver) :
    FormOnDomain.projectiveFormOnDomain Ω X (c ∘ r) (hc.comp hr) form =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback r (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hr)
        (FormOnDomain.projectiveFormOnDomain U X c hc form) := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  exact Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp (E := LinearTheta.BallCoordinates) (F := LinearTheta.BallCoordinates)
    (G := X.analyticModel) r (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hr) c (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X.toOver form)

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.DomainPrecomposition
