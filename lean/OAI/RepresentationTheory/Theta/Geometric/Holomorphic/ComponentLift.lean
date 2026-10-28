import OAI.RepresentationTheory.Theta.Geometric.ContinuousComponentLift
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.EtaleLifts

/-! # Component Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ComponentLift

noncomputable section

/-! Continuous finite étale branches of a holomorphic map lift
holomorphically to actual integral projective components. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem exists_holomorphic_projectiveComponent_lift
    {W M : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [TopologicalSpace M] [ChartedSpace W M] [PreconnectedSpace M] [Nonempty M]
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : P.toOver ⟶ X.toOver) [IsFinite f.left] [Etale f.left]
    (g : C(M, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver))
    (hfg : MDifferentiable 𝓘(ℂ, W) 𝓘(ℂ, X.analyticModel) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ g)) :
    ∃ (C : irreducibleComponents P.carrier) (c : C(M, (P.componentVariety C).analyticSpace)),
      MDifferentiable 𝓘(ℂ, W) 𝓘(ℂ, (P.componentVariety C).analyticModel) c ∧
      ∀ x, c x ≫ P.componentInclusionOver C = g x := by
  obtain ⟨C, c, hc⟩ := ContinuousComponentLift.exists_continuous_projectiveComponent_lift P g
  let Y := P.componentVariety C
  let i := P.componentInclusionOver C
  let fi := i ≫ f
  let : IsIntegral Y.toOver.left := Y.property
  let : Smooth Y.toOver.hom := Y.presentation.smooth
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : IsFinite fi.left := inferInstanceAs (IsFinite (i.left ≫ f.left))
  let : Etale fi.left := inferInstanceAs (Etale (i.left ≫ f.left))
  have hcomp : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fi ∘ c = AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ g := by
    funext x
    exact (Category.assoc (c x) i f).symm.trans (congrArg (· ≫ f) (hc x))
  refine ⟨C, c, ?_, hc⟩
  exact EtaleLifts.mdifferentiable_lift_of_localDiffeomorph (by simp : (ω : ℕ∞ω) ≠ 0)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fi) (AlgebraicGeometry.Cycles.Functoriality.IntrinsicEtale.Construction.isLocalDiffeomorph_nativeScheme_affineEtale fi)
    c c.continuous (hcomp ▸ hfg)

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ComponentLift
