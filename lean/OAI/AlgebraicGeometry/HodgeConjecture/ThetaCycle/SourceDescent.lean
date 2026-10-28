import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallInvariantDescent
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.HolomorphicOneDerivative
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceProjectivePairing

/-! # Source Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceDescent.CM

noncomputable section

/-! ThetaCycle: principal invariance of the actual theta one-form constructs
the full pure closed representative required by HeckeCycles. Closedness follows
from exactness and the native projective surface self-pairing. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}

theorem source_ball_one_apply (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    (BallForms.CM.sourceBallOneForm K L φ).val z (fun _ : Fin 1 => ξ) = HeckeCycles.GeometricSource.CM.thetaOneForm K L φ z.val ξ := by
  change (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv B.domainOpen 1 (BallForms.CM.sourceOpenOneForm K L φ)) z _ = _
  rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv_apply]
  have ht : Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv z ξ = ξ := by
    change mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) (chartAt HeckeCycles.GeometricSource.CM.BallChart z) z ξ = ξ
    rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source HeckeCycles.GeometricSource.CM.BallChart z)]
    exact tangentCoordChange_self (I := 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart)) (x := z) (z := z)
      (v := ξ) (mem_extChartAt_source z)
  change Projection.CM.sourceThetaCovector K L φ z.val (Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv z ξ) = _
  rw [ht]
  exact Projection.CM.source_theta_covector_apply K L φ z.val ξ

theorem exists_source_theta_descent (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)
    (hinv : ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g),
      (BallForms.CM.sourceBallOneForm K L φ).val.pullback (BallLineAction.CM.ballPrincipalAction K B g hg.1) =
        (BallForms.CM.sourceBallOneForm K L φ).val) :
    ∃ a : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0,
      CoverPullback.CM.ballCoverPullback K B N X π hπ 1 a.val.val = BallForms.CM.sourceBallOneForm K L φ ∧
      HeckeCycles.GeometricSource.CM.RepresentsTheta K L φ X π a := by
  have hf := CoverLocalM.CM.ball_cover_real_local_diffeomorph K B N X π hπ
  obtain ⟨b, hb, _⟩ := CoverLocalM.CM.existsUnique_smooth_cover_descent π hπ.2.1 hf 1 (BallForms.CM.sourceBallOneForm K L φ)
    (BallInvariantDescent.CM.ball_fiber_covectors_of_principal_invariance K B N X π hπ 1 (BallForms.CM.sourceBallOneForm K L φ) hinv)
  have hpb : CoverPullback.CM.ballCoverPullback K B N X π hπ 1 b = BallForms.CM.sourceBallOneForm K L φ := hb
  have hraw : b.val.pullback (E := HeckeCycles.GeometricSource.CM.BallChart) π = (BallForms.CM.sourceBallOneForm K L φ).val :=
    congrArg Subtype.val hpb
  have hp : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace 1 0 b.val := by
    apply CoverPure.CM.raw_form_pure_of_cover_pullback π hπ.2.1 (CoverLocalM.CM.ball_cover_local_diffeomorph K B N X π hπ)
    rw [hraw]
    exact BallForms.CM.source_ball_one_pure K L φ
  have hdp : CoverPullback.CM.ballCoverPullback K B N X π hπ 2 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (BallForms.CM.sourceBallOneForm K L φ) := by
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback π _ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) = _
    rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback]
    exact congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d hpb
  have hdt : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace 2 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b).val := by
    apply CoverPure.CM.raw_form_pure_of_cover_pullback π hπ.2.1 (CoverLocalM.CM.ball_cover_local_diffeomorph K B N X π hπ)
    rw [show (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b).val.pullback (E := HeckeCycles.GeometricSource.CM.BallChart) π =
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (BallForms.CM.sourceBallOneForm K L φ)).val from congrArg Subtype.val hdp]
    exact HolomorphicOneDerivative.CM.source_ball_one_derivative_pure K L φ
  have hc := SurfaceProjectivePairing.CM.projective_surface_one_form_closed_of_derivative_pure ⟨X, hπ.1⟩ b hdt
  let a : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0 := ⟨⟨b, hc⟩, hp⟩
  refine ⟨a, hpb, ?_⟩
  intro z ξ
  have h := congrArg (fun f : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 1 => f z (fun _ => ξ)) hraw
  exact h.trans (source_ball_one_apply K L φ z ξ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceDescent.CM
