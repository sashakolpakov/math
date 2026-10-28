import OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction
import OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
import OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle

/-! # Coordinate Frame Action -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.CoordinateFrameAction

/-! The actual geometric frame covariance in the constructed symplectic
coordinates gives its two block equations. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate
open OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Siegel OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem coordinate_frame_action (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball)
    (a : BallGeometryData.FrameIndex A → ℂ) :
    ComplexIntrinsicAction.Coordinate.complexifiedLinear (RealSymplecticAction.realCoordinateAction A P g).toLinearMap
      ((PeriodCoordinates.coordinateHodgeMatrix A P z).mulVec a) =
    (PeriodCoordinates.coordinateHodgeMatrix A P (GeometricGroup.geometricBallHom A g • z)).mulVec
      ((BallGeometryData.frameMatrix A g z).mulVec a) := by
  apply (ComplexPhaseCoordinates.complexPhaseCoordinates A P).injective
  rw [ComplexIntrinsicAction.Coordinate.complex_coordinate_action, PeriodCoordinates.complex_coordinate_frame, PeriodCoordinates.complex_coordinate_frame]
  exact GeometricFrameCocycle.HodgeCovariance.geometric_frame_covariance A g z a

theorem siegel_frame_action (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball)
    (a : BallGeometryData.FrameIndex A → ℂ) :
    (DataTheta.blockMatrix (RealSymplecticAction.realSymplecticBlocks A P g).complexify).mulVec
      (Sum.elim ((PeriodCoordinates.hodgeMomentum A P z).mulVec a) ((PeriodCoordinates.hodgePosition A P z).mulVec a)) =
    Sum.elim ((PeriodCoordinates.hodgeMomentum A P (GeometricGroup.geometricBallHom A g • z)).mulVec
      ((BallGeometryData.frameMatrix A g z).mulVec a))
      ((PeriodCoordinates.hodgePosition A P (GeometricGroup.geometricBallHom A g • z)).mulVec
      ((BallGeometryData.frameMatrix A g z).mulVec a)) := by
  have hs (w : BallNatural.Ball) (b : BallGeometryData.FrameIndex A → ℂ) :
      Sum.elim ((PeriodCoordinates.hodgeMomentum A P w).mulVec b) ((PeriodCoordinates.hodgePosition A P w).mulVec b) =
      DataTheta.swapPhase ((PeriodCoordinates.coordinateHodgeMatrix A P w).mulVec b) := by
    funext i
    cases i <;> rfl
  rw [hs, ComplexIntrinsicAction.Siegel.complex_siegel_action, coordinate_frame_action, hs]

theorem hodge_frame_blocks (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    (RealSymplecticAction.realSymplecticBlocks A P g).complexify.A * PeriodCoordinates.hodgeMomentum A P z +
      (RealSymplecticAction.realSymplecticBlocks A P g).complexify.B * PeriodCoordinates.hodgePosition A P z =
        PeriodCoordinates.hodgeMomentum A P (GeometricGroup.geometricBallHom A g • z) * BallGeometryData.frameMatrix A g z ∧
    (RealSymplecticAction.realSymplecticBlocks A P g).complexify.C * PeriodCoordinates.hodgeMomentum A P z +
      (RealSymplecticAction.realSymplecticBlocks A P g).complexify.D * PeriodCoordinates.hodgePosition A P z =
        PeriodCoordinates.hodgePosition A P (GeometricGroup.geometricBallHom A g • z) * BallGeometryData.frameMatrix A g z := by
  have h (a : BallGeometryData.FrameIndex A → ℂ) := siegel_frame_action A P g z a
  simp only [DataTheta.blockMatrix, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr] at h
  constructor
  · ext i j
    have he := congrFun (h (Pi.single j 1)) (.inl i)
    simpa only [Sum.elim_inl, Pi.add_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, Matrix.add_apply, Matrix.mulVec, Matrix.mul_apply, dotProduct] using he
  · ext i j
    have he := congrFun (h (Pi.single j 1)) (.inr i)
    simpa only [Sum.elim_inr, Pi.add_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, Matrix.add_apply, Matrix.mulVec, Matrix.mul_apply, dotProduct] using he

end RepresentationTheory.Theta.Adelic.CoordinateFrameAction

namespace RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance

/-! The period transformation and denominator identities follow from
the actual moving geometric frame, with its invertible position matrix. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction

theorem siegel_matrix_ext {I : Type} [Fintype I] {Z W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I}
    (h : Z.matrix = W.matrix) : Z = W := by
  cases Z
  cases W
  cases h
  rfl

theorem moving_frame_period {I : Type} [Fintype I] [DecidableEq I]
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ) (Z W : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (Q Q' T : Matrix I I ℂ) (hQ : Q.det ≠ 0)
    (hu : g.complexify.numerator Z.matrix * Q = W.matrix * Q' * T)
    (hl : g.complexify.denominator Z.matrix * Q = Q' * T) :
    W = g.transformSiegel Z := by
  have hn : g.complexify.numerator Z.matrix * Q =
      W.matrix * (g.complexify.denominator Z.matrix * Q) := by
    rw [hl, ← Matrix.mul_assoc]
    exact hu
  have hQi := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  have he := congrArg (fun M : Matrix I I ℂ => M * Q⁻¹) hn
  simp only [Matrix.mul_assoc, hQi, Matrix.mul_one] at he
  have hmatrix : W.matrix = (g.transformSiegel Z).matrix := by
    change W.matrix = g.complexify.numerator Z.matrix *
      (g.complexify.denominator Z.matrix)⁻¹
    rw [he, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (g.denominator_det_isUnit Z),
      Matrix.mul_one]
  exact siegel_matrix_ext hmatrix

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem geometric_denominator_frame (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    (RealSymplecticAction.realSymplecticBlocks A P g).complexify.denominator (PeriodCoordinates.geometricPeriod A P z).matrix *
      (PeriodCoordinates.geometricPositionUnit A P z).val =
    (PeriodCoordinates.geometricPositionUnit A P (GeometricGroup.geometricBallHom A g • z)).val * BallGeometryData.frameMatrix A g z := by
  have h := (hodge_frame_blocks A P g z).2
  rw [← PeriodCoordinates.geometricPeriod_frame A P z, ← Matrix.mul_assoc, ← Matrix.add_mul] at h
  exact h

theorem geometric_numerator_frame (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    (RealSymplecticAction.realSymplecticBlocks A P g).complexify.numerator (PeriodCoordinates.geometricPeriod A P z).matrix *
      (PeriodCoordinates.geometricPositionUnit A P z).val =
    (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A g • z)).matrix *
      (PeriodCoordinates.geometricPositionUnit A P (GeometricGroup.geometricBallHom A g • z)).val * BallGeometryData.frameMatrix A g z := by
  have h := (hodge_frame_blocks A P g z).1
  rw [← PeriodCoordinates.geometricPeriod_frame A P z, ← Matrix.mul_assoc, ← Matrix.add_mul] at h
  change _ = (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A g • z)).matrix *
    PeriodCoordinates.hodgePosition A P (GeometricGroup.geometricBallHom A g • z) * BallGeometryData.frameMatrix A g z
  rw [PeriodCoordinates.geometricPeriod_frame]
  exact h

theorem geometric_period_covariance (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A g • z) =
      (RealSymplecticAction.realSymplecticBlocks A P g).transformSiegel (PeriodCoordinates.geometricPeriod A P z) :=
  moving_frame_period (RealSymplecticAction.realSymplecticBlocks A P g) (PeriodCoordinates.geometricPeriod A P z)
    (PeriodCoordinates.geometricPeriod A P (GeometricGroup.geometricBallHom A g • z))
    (PeriodCoordinates.geometricPositionUnit A P z).val
    (PeriodCoordinates.geometricPositionUnit A P (GeometricGroup.geometricBallHom A g • z)).val (BallGeometryData.frameMatrix A g z)
    (PeriodCoordinates.hodgePosition_det_ne_zero A P z)
    (geometric_numerator_frame A P g z) (geometric_denominator_frame A P g z)

end RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance

end

end OAI
