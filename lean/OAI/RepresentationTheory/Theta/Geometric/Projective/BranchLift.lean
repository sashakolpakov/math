import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ComponentLift
import OAI.RepresentationTheory.Theta.Geometric.OpenPullbackPoints
import OAI.RepresentationTheory.Theta.Geometric.Finite.ProjectivePresentation
import OAI.RepresentationTheory.Theta.Geometric.Geometry

/-! # Branch Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.BranchLift

noncomputable section

/-! Every continuous branch over an open projective component comes from
a holomorphic map into an actual finite étale integral projective cover. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem exists_projective_holomorphic_branch_lift
    (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates) [PreconnectedSpace Ω] [Nonempty Ω]
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (m : X.toOver ⟶ Z) [IsOpenImmersion m.left] (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Z)
    (c : Ω → X.analyticSpace) (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c)
    (b : C(Ω, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints C.cover)) (hb : ∀ x, b x ≫ C.source = c x ≫ m) :
    ∃ (Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (a : Y.toOver ⟶ C.cover) (f : Y.toOver ⟶ X.toOver)
      (l : Ω → Y.analyticSpace),
      IsFinite f.left ∧ Etale f.left ∧
      ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, Y.analyticModel) ∞ l ∧
      a ≫ C.source = f ≫ m ∧
      (∀ x, l x ≫ a = b x) ∧ (∀ x, l x ≫ f = c x) := by
  let : Smooth X.toOver.hom := X.presentation.smooth
  let V := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackOver C.source m
  let p : V ⟶ X.toOver := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight C.source m
  let q : V ⟶ C.cover := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft C.source m
  let : IsFinite C.source.left := C.finite
  let : Etale C.source.left := C.etale
  let : IsFinite p.left := inferInstanceAs (IsFinite (CategoryTheory.Limits.pullback.snd C.source.left m.left))
  let : Etale p.left := inferInstanceAs (Etale (CategoryTheory.Limits.pullback.snd C.source.left m.left))
  let P := Finite.ProjectivePresentation.finiteEtaleSmoothProjectivePresentation X.presentation.projective p
  let g : C(Ω, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :=
    ⟨fun x => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackLift C.source m (b x) (c x) (hb x),
      OpenPullbackPoints.continuous_pullbackLift_of_open C.source m b c hb b.continuous⟩
  have hpg : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p ∘ g = c := by
    funext x
    exact AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toRight C.source m (b x) (c x) (hb x)
  have hg : MDifferentiable 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p ∘ g) := by
    rw [hpg]
    exact hc.mdifferentiable (by simp)
  obtain ⟨k, l, hl, hli⟩ := Holomorphic.ComponentLift.exists_holomorphic_projectiveComponent_lift P X p g hg
  let Y := P.componentVariety k
  let i := P.componentInclusionOver k
  let a := i ≫ q
  let f := i ≫ p
  refine ⟨Y, a, f, l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsFinite (i.left ≫ p.left))
  · exact inferInstanceAs (Etale (i.left ≫ p.left))
  · exact Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hl
  · change (i ≫ q) ≫ C.source = (i ≫ p) ≫ m
    rw [Category.assoc, Category.assoc, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullback_condition]
  · intro x
    exact (Category.assoc (l x) i q).symm.trans
      ((congrArg (· ≫ q) (hli x)).trans (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toLeft C.source m (b x) (c x) (hb x)))
  · intro x
    exact (Category.assoc (l x) i p).symm.trans
      ((congrArg (· ≫ p) (hli x)).trans (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackLift_toRight C.source m (b x) (c x) (hb x)))

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.BranchLift
