import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverPure

/-! # Ball Form Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallFormDescent.CM

noncomputable section

/-! ThetaCycle: construct the unique pure closed form on the actual principal
surface from compatible ball covectors. Arithmetic theta automorphy must
still supply the explicit fiber-compatibility equation. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)

def ballCoverFiberCovector (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain n)
    (z : B.Domain) : Analysis.DifferentialForms.Manifold.Basic.FormValue X.analyticModel n :=
  CoverLocalM.CM.coverFiberCovector π (CoverLocalM.CM.ball_cover_real_local_diffeomorph K B N X π hπ) n a.val z

theorem existsUnique_ball_form_descent (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain (p + q))
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain p q a.val) (hclosed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0)
    (hcompat : ∀ z w, π z = π w →
      ballCoverFiberCovector K B N X π hπ (p + q) a z =
        ballCoverFiberCovector K B N X π hπ (p + q) a w) :
    ∃! b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace (p + q),
      CoverPullback.CM.ballCoverPullback K B N X π hπ (p + q) b = a ∧
        Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace p q b.val ∧
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b = 0 := by
  let hf := CoverLocalM.CM.ball_cover_real_local_diffeomorph K B N X π hπ
  obtain ⟨b, hb, _⟩ := CoverLocalM.CM.existsUnique_smooth_cover_descent π hπ.2.1 hf (p + q) a hcompat
  have hbp : CoverPullback.CM.ballCoverPullback K B N X π hπ (p + q) b = a := hb
  have htype : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace p q b.val := by
    apply CoverPure.CM.raw_form_pure_of_cover_pullback π hπ.2.1
      (CoverLocalM.CM.ball_cover_local_diffeomorph K B N X π hπ) b.val
    have he : b.val.pullback (E := HeckeCycles.GeometricSource.CM.BallChart) π = a.val := congrArg Subtype.val hbp
    rw [he]
    exact ha
  have hc : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b = 0 :=
    (CoverPullback.CM.ball_cover_closed_iff_pullback K B N X π hπ (p + q) b).mpr (hbp.symm ▸ hclosed)
  refine ⟨b, ⟨hbp, htype, hc⟩, ?_⟩
  intro c hc
  exact CoverPullback.CM.ball_cover_pullback_injective K B N X π hπ (p + q) (hc.1.trans hbp.symm)

theorem ball_descended_form_nonzero (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain n)
    (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm X.analyticModel X.analyticSpace n)
    (hb : CoverPullback.CM.ballCoverPullback K B N X π hπ n b = a) : b ≠ 0 ↔ a ≠ 0 := by
  rw [← hb]
  exact (map_ne_zero_iff (CoverPullback.CM.ballCoverPullback K B N X π hπ n)
    (CoverPullback.CM.ball_cover_pullback_injective K B N X π hπ n)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallFormDescent.CM
