import OAI.RepresentationTheory.Theta.Geometric.QuotientPowerFrames
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing

/-! # Power Gauge Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerGaugeGluing

noncomputable section

/-! Regular consecutive-power gauges glue the native quotient power to the
first hyperplane pullback. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem thetaQuotientPower_iso_of_gauges {X : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m) (k : ℕ)
    (U : Fin (n + 1) × Fin (m + 1) → X.Opens) (hU : iSup U = ⊤)
    (hUf : ∀ p, U p ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) p.1)
    (hUg : ∀ p, U p ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) p.2)
    (r : ∀ p, Γ(X, U p)ˣ)
    (hF : ∀ p q, U p ⊓ U q ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) p.1 q.1)
    (hG : ∀ p q, U p ⊓ U q ≤ g ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) p.2 q.2)
    (hr : ∀ p q,
      PowerGaugeCover.restrictRegularUnit (show U p ⊓ U q ≤ U q from inf_le_right) (r q) *
          PowerGaugeCover.restrictRegularUnit (hF p q) (PowerGauge.projectivePullbackTransitionUnit f p.1 q.1) ^ (k + 1) =
      PowerGaugeCover.restrictRegularUnit (show U p ⊓ U q ≤ U p from inf_le_left) (r p) *
          PowerGaugeCover.restrictRegularUnit (hG p q) (PowerGauge.projectivePullbackTransitionUnit g p.2 q.2) ^ k) :
    Nonempty (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule (AlgebraicQuotient.algebraicThetaQuotient f g).sheaf k ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n 1)).sheaf) := by
  let a : ∀ p q, Γ(X, U p ⊓ U q)ˣ := fun p q =>
    (PowerGaugeCover.restrictRegularUnit (hG p q) (PowerGauge.projectivePullbackTransitionUnit g p.2 q.2) *
      (PowerGaugeCover.restrictRegularUnit (hF p q) (PowerGauge.projectivePullbackTransitionUnit f p.1 q.1))⁻¹) ^ k
  let b : ∀ p q, Γ(X, U p ⊓ U q)ˣ := fun p q =>
    PowerGaugeCover.restrictRegularUnit (hF p q) (PowerGauge.projectivePullbackTransitionUnit f p.1 q.1)
  apply IntrinsicFrame.UnitGluing.exists_iso_of_open_framed_units _ _ U hU
    (fun p => QuotientPowerFrames.thetaQuotientPowerFrameOn f g p.1 p.2 (U p) (hUf p) (hUg p) k)
    (fun p => TwistFramesOnSubopens.algebraicPullbackTwistFrameOn f 1 p.1 (U p) (hUf p)) r
    (fun p q => (a p q : Γ(X, U p ⊓ U q))) (fun p q => (b p q : Γ(X, U p ⊓ U q)))
  · intro p q
    rw [QuotientPowerFrames.thetaQuotientPowerFrameOn_restrict, QuotientPowerFrames.thetaQuotientPowerFrameOn_restrict]
    exact QuotientPowerFrames.thetaQuotientPowerFrameOn_transition f g p.1 q.1 p.2 q.2 (U p ⊓ U q) (hF p q) (hG p q) k
  · intro p q
    rw [TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict, TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict]
    have hh := TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_transition f 1 p.1 q.1 (U p ⊓ U q) (hF p q)
    simpa only [zpow_one] using hh
  · intro p q
    have hh := FramedUnitGluing.consecutivePowerGauge_identity k
      (PowerGaugeCover.restrictRegularUnit (hF p q) (PowerGauge.projectivePullbackTransitionUnit f p.1 q.1))
      (PowerGaugeCover.restrictRegularUnit (hG p q) (PowerGauge.projectivePullbackTransitionUnit g p.2 q.2))
      (PowerGaugeCover.restrictRegularUnit (show U p ⊓ U q ≤ U p from inf_le_left) (r p))
      (PowerGaugeCover.restrictRegularUnit (show U p ⊓ U q ≤ U q from inf_le_right) (r q)) (hr p q)
    exact congrArg Units.val (by simpa only [div_eq_mul_inv] using hh)

end

end OAI.RepresentationTheory.Theta.Geometric.PowerGaugeGluing
