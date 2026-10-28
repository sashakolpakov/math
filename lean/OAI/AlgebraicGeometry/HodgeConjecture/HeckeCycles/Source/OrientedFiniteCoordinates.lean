import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.OrientedTraceFrame
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.TracePhase
import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex

/-! # Oriented Finite Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.OrientedFiniteCoordinates.CM

noncomputable section

/-! The actual finite trace coordinates, with the source's index and
orientation, restrict to the constructed rational symplectic frame. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def native (x : GeometricSource.CM.Vec E) : (Fin 3 ⊕ Fin 3) → QuadraticConjugation.CM.Field.RealField E :=
  (GlobalFrames.CM.rational E (OppositeCoordinates.CM.coordinates E C)).coordinates
    (TensorPairing.CM.tensorVector E (OppositeCoordinates.CM.coordinates E C) x)

def coordinates (x : (Fin 3 ⊕ Fin 3) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E)) :
    (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex
    ((TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)).symm.sumCongr
      (TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)).symm)
    (Finite.TracePhase.CM.coordinates (QuadraticConjugation.CM.Field.RealField E) 3 x)

theorem rational_frame (x : GeometricSource.CM.Vec E) (i : GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) :
    Finite.TracePhase.CM.Rational.rational (QuadraticConjugation.CM.Field.RealField E) 3 (native E C x)
      (((TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)).sumCongr
        (TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C))) i) =
      OrientedTraceFrame.CM.frame E C x i := by
  cases i <;> rfl

theorem coordinates_rational (x : GeometricSource.CM.Vec E) :
    CM.coordinates E C (fun i =>
      algebraMap (QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E))
        (native E C x i)) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (OrientedTraceFrame.CM.frame E C x) := by
  unfold CM.coordinates
  rw [Finite.TracePhase.CM.Rational.coordinates_rational]
  funext i
  exact congrArg (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (rational_frame E C x i)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.OrientedFiniteCoordinates.CM
