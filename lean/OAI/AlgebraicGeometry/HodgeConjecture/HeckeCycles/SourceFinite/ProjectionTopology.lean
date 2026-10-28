import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ReferenceActiveWeil
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.UnitaryProjectionTopology
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticActionContinuity

/-! # Projection Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.ProjectionTopology.CM

noncomputable section

/-! Continuity of the actual finite symplectic action in the original
source coordinates, with no compatibility or continuity assumption. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem assembled : Continuous (fun g : Product.CM.FiniteGroup E C =>
    (FieldAction.CM.assembled E C g).val) :=
  Finite.UnitaryProjectionTopology.CM.assembled_matrix (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticConjugation.CM.Field.discriminant E C) 3 1
    (Source.QuadraticForms.CM.hermitianForm E C) (Source.QuadraticForms.CM.skewForm E C) (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E C)
    (Source.Characters.CM.characters E C) (Source.GlobalFrames.CM.frames E C)
    (Source.NormalizedSplittings.CM.splittings E C)

theorem trace_action (v : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Continuous (fun g : Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C) =>
      (Projection.CM.projection E C g).val *ᵥ v) :=
  SymplecticActionContinuity.CM.reindex
    (Source.TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)).symm
    (fun g => Finite.SymplecticRestriction.CM.restriction (Source.QuadraticConjugation.CM.Field.RealField E) 3
      (FieldAction.CM.assembled E (OppositeCoordinates.CM.coordinates E C) g))
    (Finite.SymplecticTopology.CM.restriction_action (Source.QuadraticConjugation.CM.Field.RealField E) 3
      (FieldAction.CM.assembled E (OppositeCoordinates.CM.coordinates E C))
      (assembled E (OppositeCoordinates.CM.coordinates E C))) v

theorem original_action (v : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Continuous (fun g : Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C) =>
      (Source.ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E C g).val *ᵥ v) := by
  have hc := SymplecticActionContinuity.CM.conjugate
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (Source.OrientedTraceFrame.CM.matrix E C))
    (Projection.CM.projection E C) (trace_action E C) v
  exact hc.congr (fun g => congrArg (fun s : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => s.val *ᵥ v)
    (WeilConjugatedHom.CM.value
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (Source.OrientedTraceFrame.CM.matrix E C))
      (Projection.CM.projection E C) g).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.ProjectionTopology.CM
