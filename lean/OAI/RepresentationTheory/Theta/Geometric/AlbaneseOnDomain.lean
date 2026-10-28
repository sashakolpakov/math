import OAI.RepresentationTheory.Theta.Geometric.AlbaneseLift
import OAI.RepresentationTheory.Theta.Geometric.Projective.FormOnDomain

/-! # Albanese On Domain -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual algebraic Albanese theta lift pulls back to the original
theta smooth form on the whole ball domain. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hh : D.HasHolomorphicThetaData) (ha : D.HasRationalThetaCovariance)

theorem Data.ActiveHeckeThetaData.thetaAlbaneseLift_domain_pullback (φ : D.sphericalInputs) :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    Projective.FormOnDomain.projectiveFormOnDomain D.domain X cover hc
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
        (D.pel.albanesePullback hg (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ))) =
      D.thetaBallSmoothForm hh φ := by
  dsimp only
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  have h := congrArg (fun f : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace 1 => f.val)
    (D.thetaAlbaneseLift_closed_pullback hg j X component cover hcover hh ha φ)
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X.toOver
    (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
      (D.pel.albanesePullback hg (D.thetaAlbaneseLift hg j X component cover hcover hh ha φ))) =
      D.periodThetaSmoothForm X cover hcover hh ha φ at h
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing.globalSmoothForm X.toOver _) = _
  rw [h]
  exact D.periodThetaSmoothForm_pullback X cover hcover hh ha φ

end

end OAI.RepresentationTheory.Theta.Geometric
