import OAI.RepresentationTheory.Theta.Geometric.Projective.DomainNaturality
import OAI.RepresentationTheory.Theta.Geometric.Projective.DomainPrecomposition
import OAI.RepresentationTheory.Theta.Geometric.AlbaneseOnDomain

/-! # Albanese Branch Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A branch whose actual target agrees with a transformed period map
pulls the algebraic theta lift back to that transformed theta form. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hh : D.HasHolomorphicThetaData) (ha : D.HasRationalThetaCovariance)

theorem Data.ActiveHeckeThetaData.thetaAlbaneseLift_branch_pullback
    (Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (target : Y.toOver ⟶ D.pel.complexSpace)
    (l : D.domain → Y.analyticSpace)
    (hl : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, Y.analyticModel) ∞ l)
    (r : D.domain → D.domain)
    (hr : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) ∞ r)
    (htarget : ∀ x, l x ≫ target = D.totalPeriodMap j X component cover (r x))
    (φ : D.sphericalInputs) :
    Projective.FormOnDomain.projectiveFormOnDomain D.domain Y l hl
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback target
        (D.pel.albanesePullback hg (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ))) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback r (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hr) (D.thetaBallSmoothForm hh φ) := by
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  let Z := (D.pel.actualComplexAlbaneseVariety hg).variety
  let alpha := D.pel.complexAlbaneseMap hg
  let m := component.hom ≫ D.componentComplexInclusion j
  have he : ∀ x, l x ≫ (target ≫ alpha) = (cover ∘ r) x ≫ (m ≫ alpha) := by
    intro x
    rw [← Category.assoc, htarget]
    change (cover (r x) ≫ (component.hom ≫ D.componentComplexInclusion j)) ≫ alpha = _
    exact Category.assoc _ _ _
  have h := Projective.DomainNaturality.projectiveFormOnDomain_eq_of_points D.domain Y X Z (target ≫ alpha)
    (m ≫ alpha) l (cover ∘ r) hl (hc.comp hr) he
    (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ)
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
  change Projective.FormOnDomain.projectiveFormOnDomain D.domain Y l hl
    (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback target
      (D.pel.albanesePullback hg (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ))) =
    Projective.FormOnDomain.projectiveFormOnDomain D.domain X (cover ∘ r) (hc.comp hr)
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
        (D.pel.albanesePullback hg (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ))) at h
  rw [Projective.DomainPrecomposition.projectiveFormOnDomain_precomp D.domain D.domain X cover r hc hr,
    D.thetaAlbaneseLift_domain_pullback hg j X component cover hcover hh ha φ] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric
