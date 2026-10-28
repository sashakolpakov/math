import OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction
import OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame
import OAI.RepresentationTheory.Theta.Adelic.RationalRealSymplectic

/-! # Geometric Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricComparison

noncomputable section

/-! Assemble the actual trace coordinates, geometric period, Hodge frame,
and half-determinant frame. These identifications hold independently of
the subsequently supplied archimedean test functions. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.RationalSymplecticAction OAI.RepresentationTheory.Theta.Adelic.RationalRealSymplectic
open OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic OAI.RepresentationTheory.Theta.Adelic.CoordinateFrameAction.PeriodCovariance
open OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)
variable (gaussian : BallNatural.Ball → (BallGeometryData.FrameIndex A → ℂ) → ThetaEvaluation.ArchimedeanTests F (3 * m))

def geometricComparison : DataTheta.ComparisonData F H K A where
  rationalPosition := MinkowskiCoordinatesPosition.rationalPositionCoordinates A
  realPosition := MinkowskiCoordinatesPosition.realPositionCoordinates A
  rationalPhase := PhaseCoordinates.rationalPhaseCoordinates A
  realPhase := PhaseCoordinates.realPhaseCoordinates A
  complexPhase := ComplexPhaseCoordinates.complexPhaseCoordinates A P
  period := PeriodCoordinates.geometricPeriod A P
  frame := PeriodCoordinates.geometricPositionUnit A P
  halfFrame := GeometricHalfFrame.geometricHalfFrame A P
  ball := (GeometricGroup.geometricBallHom A).toMonoidHom
  symplectic := RealSymplecticAction.realSymplecticBlocks A P
  rationalSymplectic := RationalSymplecticAction.rationalSymplecticBlocks A P
  gaussian := gaussian

theorem geometricComparison_coordinates :
    DataTheta.CoordinateIdentification (geometricComparison A P gaussian) P := by
  refine ⟨MinkowskiCoordinatesPosition.realPositionCoordinates_rational A, PhaseCoordinates.rationalPhaseCoordinates_inl A,
    PhaseCoordinates.rationalPhaseCoordinates_pairing A, PhaseCoordinates.realPhaseCoordinates_rational A,
    PhaseCoordinates.realPhaseCoordinates_inl A, PhaseCoordinates.realPhaseCoordinates_pairing A, ?_,
    RealSymplecticAction.realSymplecticBlocks_action A P, RationalSymplecticAction.rationalSymplecticBlocks_action A P,
    RationalRealSymplectic.rational_real_symplectic_matrix A P⟩
  exact ComplexPhaseCoordinates.complexPhaseCoordinates_native A P

theorem geometricComparison_geometry :
    DataTheta.GeometryIdentification (geometricComparison A P gaussian) := by
  refine ⟨(GeometricGroup.geometricBallHom A).continuous, GeometricGroup.geometricBallHom_matrix A,
    PeriodHolomorphic.period_matrix_holomorphic A P, PeriodHolomorphic.position_frame_holomorphic A P,
    GeometricHalfFrame.geometricHalfFrame_holomorphic A P, ?_, PeriodCoordinates.geometric_period_graph A P,
    PeriodCoordinates.geometric_period_range A P, GeometricFrameCocycle.HodgeCovariance.geometric_frame_covariance A, GeometricFrameCocycle.HodgeCovariance.geometric_frame_determinant A,
    CoordinateFrameAction.PeriodCovariance.geometric_period_covariance A P, CoordinateFrameAction.PeriodCovariance.geometric_denominator_frame A P⟩
  intro z
  exact ⟨GeometricHalfFrame.geometricHalfFrame_nonzero A P z, GeometricHalfFrame.geometricHalfFrame_square A P z⟩

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricComparison
