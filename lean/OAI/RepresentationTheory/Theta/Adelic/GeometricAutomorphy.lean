import OAI.RepresentationTheory.Theta.Adelic.GeometricComparison
import OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare

/-! # Geometric Automorphy -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.GeometricAutomorphy

/-! The natural geometric half-line action gives an independently
constructed determinant branch in the actual symplectic coordinates. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance
open OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction
open OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare OAI.RepresentationTheory.Theta.Adelic.BallNatural.LineLift

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def geometricFactor (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) : ℂ :=
  BallNatural.Factors.naturalHalfFactor m (GeometricGroup.geometricBallHom A g) z *
    GeometricHalfFrame.geometricHalfFrame A P (GeometricGroup.geometricBallHom A g • z) / GeometricHalfFrame.geometricHalfFrame A P z

theorem geometricFactor_nonzero (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    geometricFactor A P g z ≠ 0 :=
  div_ne_zero (mul_ne_zero (pow_ne_zero m (BallNatural.Factors.automorphyFactor_ne_zero _ _))
    (GeometricHalfFrame.geometricHalfFrame_nonzero A P _)) (GeometricHalfFrame.geometricHalfFrame_nonzero A P z)

theorem geometricFactor_square (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    geometricFactor A P g z ^ 2 =
      ((RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (PeriodCoordinates.geometricPeriod A P z).matrix).det := by
  have h := congrArg Matrix.det (CoordinateFrameAction.PeriodCovariance.geometric_denominator_frame A P g z)
  rw [Matrix.det_mul, Matrix.det_mul, GeometricFrameCocycle.HodgeCovariance.geometric_frame_determinant] at h
  rw [geometricFactor, div_pow, mul_pow, BallNatural.Factors.naturalHalfFactor_sq,
    GeometricHalfFrame.geometricHalfFrame_square, GeometricHalfFrame.geometricHalfFrame_square]
  apply (div_eq_iff (PeriodCoordinates.hodgePosition_det_ne_zero A P z)).mpr
  exact (mul_comm _ _).trans h.symm

theorem geometricFactor_mul (g h : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    geometricFactor A P (g * h) z =
      geometricFactor A P g (GeometricGroup.geometricBallHom A h • z) * geometricFactor A P h z := by
  simp only [geometricFactor, map_mul, mul_smul, BallNatural.Factors.naturalHalfFactor_mul]
  field_simp [GeometricHalfFrame.geometricHalfFrame_nonzero A P (GeometricGroup.geometricBallHom A h • z)]

theorem geometricFactor_one (z : BallNatural.Ball) : geometricFactor A P 1 z = 1 := by
  simp only [geometricFactor, map_one, one_smul, BallNatural.Factors.naturalHalfFactor,
    BallNatural.Factors.automorphyFactor_one, one_pow, one_mul]
  exact div_self (GeometricHalfFrame.geometricHalfFrame_nonzero A P z)

theorem geometricFactor_natural (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) (a : ℂ) :
    (geometricFactor A P g z * GeometricHalfFrame.geometricHalfFrame A P z /
      GeometricHalfFrame.geometricHalfFrame A P (GeometricGroup.geometricBallHom A g • z)) * a =
    (BallNatural.LineLift.naturalLineLift m (GeometricGroup.geometricBallHom A g) (z, a)).2 := by
  change _ = BallNatural.Factors.naturalHalfFactor m (GeometricGroup.geometricBallHom A g) z * a
  rw [geometricFactor]
  field_simp [GeometricHalfFrame.geometricHalfFrame_nonzero A P z,
    GeometricHalfFrame.geometricHalfFrame_nonzero A P (GeometricGroup.geometricBallHom A g • z)]

theorem geometricFactor_continuous :
    Continuous (fun p : RationalSU.ArchimedeanSU F H × BallNatural.Ball => geometricFactor A P p.1 p.2) := by
  have hhalf := BallHolomorphicSquare.ball_holomorphic_continuous _ (GeometricHalfFrame.geometricHalfFrame_holomorphic A P)
  have hball : Continuous (fun p : RationalSU.ArchimedeanSU F H × BallNatural.Ball =>
      (GeometricGroup.geometricBallHom A p.1, p.2)) :=
    ((GeometricGroup.geometricBallHom A).continuous.comp continuous_fst).prodMk continuous_snd
  exact (((BallNatural.Factors.naturalHalfFactor_continuous m).comp hball).mul
    (hhalf.comp (continuous_smul.comp hball))).div (hhalf.comp continuous_snd)
    (fun p => GeometricHalfFrame.geometricHalfFrame_nonzero A P p.2)

end RepresentationTheory.Theta.Adelic.GeometricAutomorphy

namespace RepresentationTheory.Theta.Adelic.GeometricAutomorphy.Holomorphic

/-! Holomorphy of the geometric determinant branch follows from its
continuous nonzero square and the actual holomorphic period map. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.GeometricAutomorphy
open OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem geometric_denominator_holomorphic (g : RationalSU.ArchimedeanSU F H) :
    BallGeometryData.BallHolomorphic (fun z =>
      ((RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (PeriodCoordinates.geometricPeriod A P z).matrix).det) := by
  have hdet : Differentiable ℂ (fun M : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ =>
      ((RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator M).det) := by
    simp only [Matrix.det_apply', AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator,
      Matrix.add_apply, Matrix.mul_apply]
    fun_prop
  have hc := hdet.comp_differentiableOn (PeriodHolomorphic.period_matrix_holomorphic A P)
  apply hc.congr
  intro z hz
  simp only [Function.comp_apply, dite_eq_left hz]

theorem geometricFactor_holomorphic (g : RationalSU.ArchimedeanSU F H) :
    BallGeometryData.BallHolomorphic (geometricFactor A P g) := by
  have hc : Continuous (geometricFactor A P g) :=
    BallHolomorphicSquare.continuous_fixed_left (geometricFactor A P) (geometricFactor_continuous A P) g
  exact BallHolomorphicSquare.ball_holomorphic_of_continuous_square (geometricFactor A P g)
    (fun z => ((RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (PeriodCoordinates.geometricPeriod A P z).matrix).det)
    hc (geometric_denominator_holomorphic A P g)
    (geometricFactor_square A P g) (geometricFactor_nonzero A P g)

end RepresentationTheory.Theta.Adelic.GeometricAutomorphy.Holomorphic

end

end OAI
