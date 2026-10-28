import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.LiftDetection
import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-! # Gaussian Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GaussianLift.CM

noncomputable section

/-! The real lift constructed from the original source frame acts on
the actual Siegel Gaussian with the source's explicit scalar. Its group
law follows from that scalar's cocycle and the genuine two-fold cover. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarCocycle.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealLift.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

theorem gaussian_nonzero (z : GeometricSource.CM.BallChart) : RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest W (L.period z) 0 ≠ 0 := by
  intro h
  have he := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (GeometricSource.CM.Positions E places) => f.val 0) h
  rw [RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest_apply, RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.gaussianFunction_zero] at he
  exact one_ne_zero he

theorem realLift_gaussian (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    W.real.action (RealLift.CM.realLift E L W g) (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest W (L.period z) 0) =
      ScalarCocycle.CM.sourceScalar E L g z • RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest W (L.period (UnitaryEq.CM.Frames.period E g z)) 0 := by
  rw [RealLift.CM.realLift_action, RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.realAction_gaussian, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor_zero, inv_one, mul_one,
    map_zero, smul_smul, ← ScalarCocycle.CM.sourceScalar_eq_signed_halfDet E L g z hz,
    ← UnitaryEq.CM.PeriodCovariance.period_covariance E L g z hz]

theorem realLift_one : RealLift.CM.realLift E L W (1 : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) = 1 := by
  apply Real.LiftDetection.CM.real_eq_of_nonzero_vector W _ _ (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest W (L.period 0) 0)
    (gaussian_nonzero E L W 0)
  · rw [RealLift.CM.realLift_covers, ComplexAction.CM.Symplectic.symplectic_one, map_one, map_one]
  · rw [realLift_gaussian E L W 1 0 (MultiplierSign.CM.zero_mem_domain E), ScalarCocycle.CM.sourceScalar_one, ScalarCocycle.CM.period_one,
      one_smul, map_one]
    rfl

theorem realLift_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    RealLift.CM.realLift E L W (g * h) = RealLift.CM.realLift E L W g * RealLift.CM.realLift E L W h := by
  apply Real.LiftDetection.CM.real_eq_of_nonzero_vector W _ _ (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest W (L.period 0) 0)
    (gaussian_nonzero E L W 0)
  · rw [RealLift.CM.realLift_covers, map_mul, RealLift.CM.realLift_covers, RealLift.CM.realLift_covers, ComplexAction.CM.Symplectic.symplectic_mul, map_mul]
  · rw [map_mul, LinearEquiv.mul_apply, realLift_gaussian E L W (g * h) 0 (MultiplierSign.CM.zero_mem_domain E),
      realLift_gaussian E L W h 0 (MultiplierSign.CM.zero_mem_domain E), map_smul,
      realLift_gaussian E L W g (UnitaryEq.CM.Frames.period E h 0) (UnitaryEq.CM.PrescribedAction.period_preserves E h 0 (MultiplierSign.CM.zero_mem_domain E)),
      ScalarCocycle.CM.sourceScalar_mul E L g h 0 (MultiplierSign.CM.zero_mem_domain E), ScalarCocycle.CM.period_mul, smul_smul,
      mul_comm (ScalarCocycle.CM.sourceScalar E L g (UnitaryEq.CM.Frames.period E h 0))]

def realHom : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →* MpR where
  toFun := RealLift.CM.realLift E L W
  map_one' := realLift_one E L W
  map_mul' := realLift_mul E L W

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.GaussianLift.CM
