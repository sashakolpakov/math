import OAI.RepresentationTheory.Theta.Geometric.Rational.DomainSmooth
import OAI.RepresentationTheory.Theta.Geometric.Projective.FormOnDomain

/-! # Theta Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The smooth pullback of the original theta form has exactly the
rational period derivative appearing in the finite Weil covariance sum. -/

set_option backward.isDefEq.respectTransparency false
open scoped _root_.Manifold ContDiff

theorem Rational.ThetaPullback.periodChartEvaluation_apply (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates)
    (x : Ω) (u : LinearTheta.BallCoordinates) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm LinearTheta.BallCoordinates Ω 1) :
    Projective.FormOnDomain.periodChartEvaluation Ω x u form = form x (fun _ => u) := by
  have h := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue LinearTheta.BallCoordinates 1 => a (fun _ => u))
    (Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_symm_eq_inChart form.val (chartAt LinearTheta.BallCoordinates x)
      (chart_mem_atlas LinearTheta.BallCoordinates x) x)
  have hi : (Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv x).symm u = u :=
    (Complex.CovectorForms.openTangentEquiv_apply_id Ω x ((Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv x).symm u)).symm.trans
      ((Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv x).apply_symm_apply u)
  change form x (fun _ => (Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv x).symm u) = Projective.FormOnDomain.periodChartEvaluation Ω x u form at h
  rw [hi] at h
  exact h.symm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.thetaBallSmoothForm_apply (hh : D.HasHolomorphicThetaData)
    (φ : D.sphericalInputs) (x : D.domain) (v : Fin 1 → LinearTheta.BallCoordinates) :
    D.thetaBallSmoothForm hh φ x v = D.thetaUniversal φ.val x.val (v 0) :=
  Complex.CovectorForms.holomorphicCovectorManifoldForm_apply D.domain (D.thetaUniversal φ.val) _ x v

theorem Data.ActiveHeckeThetaData.rationalThetaPullback_chart (hh : D.HasHolomorphicThetaData)
    (g : D.RationalSU) (φ : D.sphericalInputs) (x : D.domain) (u : LinearTheta.BallCoordinates) :
    Projective.FormOnDomain.periodChartEvaluation D.domain x u
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (D.rationalPeriodPoint g)
        (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex (D.rationalPeriodPoint_contMDiff g))
        (D.thetaBallSmoothForm hh φ)) =
      D.thetaUniversal φ.val (D.periodMap g x.val) (fderiv ℂ (D.periodMap g) x.val u) := by
  rw [Rational.ThetaPullback.periodChartEvaluation_apply]
  change D.thetaBallSmoothForm hh φ (D.rationalPeriodPoint g x)
    (fun _ => mfderiv 𝓘(ℝ, LinearTheta.BallCoordinates) 𝓘(ℝ, LinearTheta.BallCoordinates)
      (D.rationalPeriodPoint g) x u) = _
  rw [D.thetaBallSmoothForm_apply]
  rw [AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars.real_mfderiv_apply_eq_complex
    (((D.rationalPeriodPoint_contMDiff g).of_le (by simp)).contMDiffAt)]
  change D.thetaUniversal φ.val (D.periodMap g x.val)
    (mfderiv 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, LinearTheta.BallCoordinates) (D.periodDomainMap g) x u) = _
  rw [D.periodDomainMap_mfderiv]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
