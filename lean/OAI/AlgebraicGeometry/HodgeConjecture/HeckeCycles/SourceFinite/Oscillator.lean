import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FunctionUnitarity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OscillatorHomAssembly

/-! # Oscillator -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Oscillator.CM

noncomputable section

/-! The actual source finite action lifts to the genuine oscillator
group by its proved Haar unitarity and Heisenberg covariance. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def lift : Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C) →*
    Finite.FiniteOscillator.CM.Oscillator (I := GeometricSource.CM.Positions E places) :=
  OscillatorHomAssembly.CM.lift (I := GeometricSource.CM.Positions E places)
    (Projection.CM.projection E C)
    (Source.TraceAction.CM.traceAction E (OppositeCoordinates.CM.coordinates E C))
    (Source.FunctionUnitarity.CM.trace_unitary E (OppositeCoordinates.CM.coordinates E C))
    (Source.TraceCovariance.CM.covariance E C)

theorem projection_matrix
    (g : Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C)) :
    (Finite.FiniteOscillator.CM.projection (lift E C g)).val =
      (Projection.CM.projection E C g).val :=
  OscillatorHomAssembly.CM.projection_matrix _ _ _ _ g

theorem action
    (g : Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C)) :
    Finite.FiniteOscillator.CM.action (lift E C g) =
      Source.TraceAction.CM.traceAction E (OppositeCoordinates.CM.coordinates E C) g := rfl

theorem rational_projection (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (Finite.FiniteOscillator.CM.projection
      (lift E C (Source.RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g))).val =
      (Source.OrientedTraceFrame.CM.matrix E C * Source.ComplexAction.CM.Symplectic.symplectic E C g *
        (Source.OrientedTraceFrame.CM.matrix E C)⁻¹).val.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :=
  (projection_matrix E C _).trans (congrArg Subtype.val (Projection.CM.rational_projection E C g))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Oscillator.CM
