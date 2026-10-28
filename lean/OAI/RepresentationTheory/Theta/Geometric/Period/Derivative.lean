import OAI.RepresentationTheory.Theta.Geometric.Period.SmoothTheta
import OAI.RepresentationTheory.Theta.Geometric.BidegreeCoverReflection
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CovectorDerivative

/-! # Derivative -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The genuine descended theta form has a derivative of type (2,0).
This follows on the ball from holomorphy and descends by the actual
surjective holomorphic period differential. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (hh : D.HasHolomorphicThetaData) (ha : D.HasRationalThetaCovariance)

theorem Data.ActiveHeckeThetaData.periodThetaSmoothForm_pullback (φ : D.sphericalInputs) :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
      (D.periodThetaSmoothForm X cover hcover hh ha φ) = D.thetaBallSmoothForm hh φ := by
  dsimp only
  apply Subtype.ext
  exact D.periodThetaRaw_pullback X cover hcover hh ha φ

theorem Data.ActiveHeckeThetaData.periodThetaSmoothForm_derivative_pure (φ : D.sphericalInputs) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace 2 0
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (D.periodThetaSmoothForm X cover hcover hh ha φ)).val := by
  have hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  apply BidegreeCoverReflection.manifoldBidegree_of_surjective_pullback _ cover (hc.of_le (by simp)) hcover.1
    (fun x => (hcover.2.2.2.1 x).surjective)
  have h := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (D.periodThetaSmoothForm_pullback X cover hcover hh ha φ)
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback] at h
  have hv := congrArg (fun a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm LinearTheta.BallCoordinates D.domain 2 => a.val) h
  exact (congrArg (Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree LinearTheta.BallCoordinates D.domain 2 0) hv).mpr
    (Holomorphic.CovectorDerivative.holomorphicCovectorManifoldForm_derivative_pure D.domain (D.thetaUniversal φ.val)
      (LinearTheta.canonical_oneForm_holomorphic D.domain D.period hh.1 D.project hh.2 φ.val))

end

end OAI.RepresentationTheory.Theta.Geometric
