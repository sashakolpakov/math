import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallLineAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocalM
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallFormDescent

/-! # Ball Invariant Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallInvariantDescent.CM

noncomputable section

/-! ThetaCycle: the literal principal-group invariance equation supplies the
fiber-covector compatibility required for descent to an actual ball cover. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)

theorem ball_fiber_covectors_of_principal_invariance (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain n)
    (ha : ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g),
      a.val.pullback (BallLineAction.CM.ballPrincipalAction K B g hg.1) = a.val) :
    ∀ z w, π z = π w → BallFormDescent.CM.ballCoverFiberCovector K B N X π hπ n a z =
      BallFormDescent.CM.ballCoverFiberCovector K B N X π hπ n a w := by
  intro z w hzw
  obtain ⟨g, hg, hact⟩ := (hπ.2.2.2.2.2 z w).mp hzw
  have hw : w = BallLineAction.CM.ballPrincipalAction K B g hg.1 z := Subtype.ext hact
  rw [hw]
  exact CoverLocalM.CM.cover_fiber_covector_deck_invariant π
    (CoverLocalM.CM.ball_cover_real_local_diffeomorph K B N X π hπ)
    (BallLineAction.CM.ballPrincipalAction K B g hg.1) (BallLineAction.CM.ball_principal_action_smooth K B g hg.1)
    (BallLineAction.CM.ball_principal_action_over_cover K B g N hg X π hπ) n a.val (ha g hg) z

theorem existsUnique_invariant_ball_form_descent (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain (p + q))
    (hp : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain p q a.val)
    (hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    (ha : ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g),
      a.val.pullback (BallLineAction.CM.ballPrincipalAction K B g hg.1) = a.val) :
    ∃! b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace (p + q),
      CoverPullback.CM.ballCoverPullback K B N X π hπ (p + q) b = a ∧
        Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace p q b.val ∧
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b = 0 :=
  BallFormDescent.CM.existsUnique_ball_form_descent K B N X π hπ p q a hp hc
    (ball_fiber_covectors_of_principal_invariance K B N X π hπ (p + q) a ha)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallInvariantDescent.CM
