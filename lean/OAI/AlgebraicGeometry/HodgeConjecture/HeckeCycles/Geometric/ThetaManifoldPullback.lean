import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms
import OAI.RepresentationTheory.Theta.Geometric.BidegreeCoverReflection

/-! # Theta Manifold Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaManifoldPullback.CM

noncomputable section

/-! Express the native period covector identity as literal evaluation
of the smooth manifold form on the derivative of the period cover. -/

open scoped Classical _root_.Manifold ContDiff
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Theta.Geometric.BidegreeCoverReflection OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]

theorem apply (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (φ : D.sphericalInputs) (x : D.domain) (ξ : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    (CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety D hg Θ j X component φ).val (cover x)
      (fun _ : Fin 1 => mfderiv 𝓘(ℝ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℝ, X.analyticModel) cover x ξ) =
      D.thetaUniversal φ.val x.val ξ := by
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  have hraw := congrArg (fun f : Analysis.DifferentialForms.Manifold.Basic.FormValue RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates 1 => f (fun _ => ξ))
    (RepresentationTheory.Theta.Geometric.BidegreeCoverReflection.rawForm_preferred_value (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
      (CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety D hg Θ j X component φ)).val x)
  exact hraw.symm.trans (CMExtraction.Intrinsic.PeriodForms.thetaOnPeriodVariety_covector D hg Θ j X component cover hcover hΘ φ x ξ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaManifoldPullback.CM
