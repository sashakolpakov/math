import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarCalibration
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.Principal
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OppositeCoordinates

/-! # Reference Scalar Calibration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceScalarCalibration.CM

noncomputable section

/-! Calibration on the actual matched reference lattice. The original
period, rational action and finite input are retained even when the
reference lattice differs from the source lattice. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DescendedInvariance.CM

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice)

theorem invariant (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ) (π : B.Domain → X.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover N X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (hg : (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2).principalLevel N
      (Matrix.SpecialLinearGroup.toLin' g.val)) (z : B.Domain) (ξ : GeometricSource.CM.BallChart) :
    GeometricSource.CM.thetaOneForm E L φ (Source.UnitaryEq.CM.Frames.period E g z.val) (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z.val ξ) =
      GeometricSource.CM.thetaOneForm E L φ z.val ξ := by
  have hp : π ∘ Source.DescendedInvariance.CM.ballMap E g = π := by
    funext w
    exact ((hπ.2.2.2.2.2 w (Source.DescendedInvariance.CM.ballMap E g w)).mpr
      ⟨Matrix.SpecialLinearGroup.toLin' g.val, hg, Source.DescendedInvariance.CM.period_eq_lineAction E g w.val w.property⟩).symm
  have hd := mfderiv_comp (I := 𝓘(ℝ, GeometricSource.CM.BallChart)) (I' := 𝓘(ℝ, GeometricSource.CM.BallChart))
    (I'' := 𝓘(ℝ, X.analyticModel)) z
    (Theta.Matching.CM.mdifferentiableAt_real (hπ.2.2.2.1 (Source.DescendedInvariance.CM.ballMap E g z)))
    (Theta.Matching.CM.mdifferentiableAt_real (Source.DescendedInvariance.CM.ballMap_differentiable E g z))
  change (show GeometricSource.CM.BallChart →L[ℝ] X.analyticModel from
    mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) (π ∘ Source.DescendedInvariance.CM.ballMap E g) z) =
      (show GeometricSource.CM.BallChart →L[ℝ] X.analyticModel from
        mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π (Source.DescendedInvariance.CM.ballMap E g z)).comp
      (show GeometricSource.CM.BallChart →L[ℝ] GeometricSource.CM.BallChart from
        mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, GeometricSource.CM.BallChart) (Source.DescendedInvariance.CM.ballMap E g) z) at hd
  erw [hp, Theta.Matching.CM.real_mfderiv_eq_complex (Source.DescendedInvariance.CM.ballMap_differentiable E g z),
    Source.DescendedInvariance.CM.ballMap_derivative E g z] at hd
  have hz : π (Source.DescendedInvariance.CM.ballMap E g z) = π z := congrFun hp z
  change GeometricSource.CM.thetaOneForm E L φ (Source.DescendedInvariance.CM.ballMap E g z).val
    (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z.val ξ) = GeometricSource.CM.thetaOneForm E L φ z.val ξ
  rw [← hω (Source.DescendedInvariance.CM.ballMap E g z) (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z.val ξ), ← hω z ξ, hz]
  congr 1
  funext i
  exact (congrArg (fun A : GeometricSource.CM.BallChart →L[ℝ] X.analyticModel => A ξ) hd).symm

theorem scalar_one (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ) (π : B.Domain → X.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover N X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω)
    (hne : ∃ z ∈ B.domain, ∃ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ ≠ 0)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (hg : (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2).principalLevel N
      (Matrix.SpecialLinearGroup.toLin' g.val))
    (c : ℂ) (hc : Source.WeilData.CM.finiteAction E L g (Theta.Weil.CM.finiteWeilInput φ) =
      c • Theta.Weil.CM.finiteWeilInput φ) : c = 1 := by
  obtain ⟨z, hz, ξ, hvalue⟩ := hne
  have h := Source.WeilData.CM.source_covariance E L g φ z hz ξ
  rw [hc, map_smul] at h
  change c * RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
    (Theta.Weil.CM.finiteWeilInput φ) (Source.UnitaryEq.CM.Frames.period E g z) (fderiv ℂ (Source.UnitaryEq.CM.Frames.period E g) z ξ) =
      GeometricSource.CM.thetaOneForm E L φ z ξ at h
  rw [Theta.Projection.CM.canonical_oneForm_eq_source,
    invariant E L P hΛ φ X N π hπ ω hω g hg ⟨z, hz⟩ ξ] at h
  exact (mul_eq_right₀ hvalue).mp h

theorem principal (hb : P.b = B.b)
    {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ P.lattice]
    (b : Module.Basis J ℤ P.lattice) (N : ℕ) (hN : 0 < N)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (hg : Source.PELFiniteGroup.CM.pel E
      (OppositeCoordinates.CM.coordinates E L.coordinates) P hb
      (Source.RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E L.coordinates) g) ∈
      P.adelicPrincipalLevel N) :
    (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2).principalLevel N
      (Matrix.SpecialLinearGroup.toLin' g.val) := by
  have h := Rational.Principal.CM.rational_principal E
    (OppositeCoordinates.CM.coordinates E L.coordinates) P hb b N hN g hg
  refine ⟨g.property, ?_, h.1, ?_⟩
  · change LinearMap.det (Matrix.toLin' g.val.val) = 1
    rw [LinearMap.det_toLin']
    exact g.val.property
  · intro x hx
    obtain ⟨y, hy, he⟩ := h.2 x hx
    refine ⟨y, hy, ?_⟩
    rw [natCast_zsmul]
    exact he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceScalarCalibration.CM
