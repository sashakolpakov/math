import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FunctionCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TraceTestHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CovarianceTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Projection

/-! # Trace Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceCovariance.CM

noncomputable section

/-! Exact covariance of the source-indexed finite Schwartz action with
the rational finite-adelic Heisenberg operators and actual projection. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem covariance
    (g : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C))
    (v : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    TraceAction.CM.traceAction E (OppositeCoordinates.CM.coordinates E C) g
      (Finite.FourierHeisenberg.CM.operator (fun i => v (.inl i)) (fun i => v (.inr i)) φ) =
      Finite.FourierHeisenberg.CM.operator
        (fun i => ((SourceFinite.Projection.CM.projection E C g).val *ᵥ v) (.inl i))
        (fun i => ((SourceFinite.Projection.CM.projection E C g).val *ᵥ v) (.inr i))
        (TraceAction.CM.traceAction E (OppositeCoordinates.CM.coordinates E C) g φ) :=
  CovarianceTransport.CM.transport
    (V := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (W := RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions (QuadraticConjugation.CM.Field.RealField E) 3)
    (P := (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (Q := (Fin 3 ⊕ Fin 3) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E))
    (TraceTests.CM.equivalence E (OppositeCoordinates.CM.coordinates E C))
    (TraceAction.CM.traceAction E (OppositeCoordinates.CM.coordinates E C) g)
    (TraceAction.CM.functionAction E (OppositeCoordinates.CM.coordinates E C) g)
    (TraceAction.CM.traceAction_intertwines E (OppositeCoordinates.CM.coordinates E C) g)
    (fun u => Finite.FourierHeisenberg.CM.operator (fun i => u (.inl i)) (fun i => u (.inr i)))
    (fun z => (Finite.TraceHeisenberg.CM.operator (QuadraticConjugation.CM.Field.RealField E) 3
      (fun i => z (.inr i)) (fun i => z (.inl i))).toLinearMap)
    (OrientedFiniteCoordinates.CM.coordinates E C)
    (TraceTestHeisenberg.CM.phases (QuadraticConjugation.CM.Field.RealField E) 3
      (TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C))).surjective
    (TraceTestHeisenberg.CM.intertwines (QuadraticConjugation.CM.Field.RealField E) 3
      (TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)))
    (fun u => (SourceFinite.Projection.CM.projection E C g).val *ᵥ u)
    (fun z => (SourceFinite.FieldAction.CM.assembled E (OppositeCoordinates.CM.coordinates E C) g).val *ᵥ z)
    (SourceFinite.Projection.CM.projection_coordinates E C g)
    (FunctionCovariance.CM.covariance E (OppositeCoordinates.CM.coordinates E C) g) v φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TraceCovariance.CM
