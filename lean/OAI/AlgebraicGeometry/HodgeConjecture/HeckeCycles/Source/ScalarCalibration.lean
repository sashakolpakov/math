import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DescendedInvariance
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData

/-! # Scalar Calibration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarCalibration.CM

noncomputable section

/-! The same nonzero descended source theta form detects the scalar
in its original rational Weil action. All covariance and invariance
come from the original construction and cover. -/

open scoped Classical _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))

theorem scalar_one
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ) (π : B.Domain → X.analyticSpace)
    (hπ : B.IsBallCover N X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω)
    (hne : ∃ z ∈ B.domain, ∃ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ ≠ 0)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (hg : B.principalLevel N (Matrix.SpecialLinearGroup.toLin' g.val))
    (c : ℂ) (hc : WeilData.CM.finiteAction E L g (Theta.Weil.CM.finiteWeilInput φ) =
      c • Theta.Weil.CM.finiteWeilInput φ) : c = 1 := by
  obtain ⟨z, hz, ξ, hvalue⟩ := hne
  have h := WeilData.CM.source_covariance E L g φ z hz ξ
  rw [hc, map_smul] at h
  change c * RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
    (Theta.Weil.CM.finiteWeilInput φ) (UnitaryEq.CM.Frames.period E g z) (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z ξ) =
      GeometricSource.CM.thetaOneForm E L φ z ξ at h
  rw [Theta.Projection.CM.canonical_oneForm_eq_source,
    DescendedInvariance.CM.invariant E L φ X N π hπ ω hω g hg ⟨z, hz⟩ ξ] at h
  exact (mul_eq_right₀ hvalue).mp h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarCalibration.CM
