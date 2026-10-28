import OAI.RepresentationTheory.Theta.Geometric.Projective.FormOnDomain
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerNaturality

/-! # Domain Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.DomainNaturality

noncomputable section

/-! Pulling algebraic forms to the ball is natural for actual projective
maps and depends only on their composite maps on complex points. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem projectiveFormOnDomain_pullback (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (X Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ Y.toOver)
    (c : Ω → X.analyticSpace)
    (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c)
    (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms Y.toOver) :
    let : IsIntegral X.toOver.left := X.property
    let : Smooth X.toOver.hom := X.presentation.smooth
    let : IsIntegral Y.toOver.left := Y.property
    let : Smooth Y.toOver.hom := Y.presentation.smooth
    FormOnDomain.projectiveFormOnDomain Ω X c hc (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      FormOnDomain.projectiveFormOnDomain Ω Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ c)
        ((AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f ∞).comp hc) form := by
  dsimp only
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : IsIntegral Y.toOver.left := Y.property
  let : Smooth Y.toOver.hom := Y.presentation.smooth
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  let : Y.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated Y
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback c (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X.toOver (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f form)) = _
  rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerNaturality.globalSmoothForm_pullback]
  exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp (E := LinearTheta.BallCoordinates)
    (F := X.analyticModel) (G := Y.analyticModel) c (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map f ∞)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm Y.toOver form)).symm

theorem projectiveFormOnDomain_eq_of_points (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (X Y Z : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ Z.toOver) (g : Y.toOver ⟶ Z.toOver)
    (c : Ω → X.analyticSpace) (d : Ω → Y.analyticSpace)
    (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c)
    (hd : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, Y.analyticModel) ∞ d)
    (h : ∀ x, c x ≫ f = d x ≫ g) (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms Z.toOver) :
    FormOnDomain.projectiveFormOnDomain Ω X c hc (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f form) =
      FormOnDomain.projectiveFormOnDomain Ω Y d hd (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback g form) := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : IsIntegral Y.toOver.left := Y.property
  let : Smooth Y.toOver.hom := Y.presentation.smooth
  let : IsIntegral Z.toOver.left := Z.property
  let : Smooth Z.toOver.hom := Z.presentation.smooth
  have he : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ c = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g ∘ d := funext h
  rw [projectiveFormOnDomain_pullback, projectiveFormOnDomain_pullback]
  simp only [he]

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.DomainNaturality
