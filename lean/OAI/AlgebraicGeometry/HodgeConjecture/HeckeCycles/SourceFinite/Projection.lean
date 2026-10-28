import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.FieldAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.OrientedFiniteCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.MatrixRationalDetermination

/-! # Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Projection.CM

noncomputable section

/-! An actual finite symplectic representation of the source unitary
group in the oriented trace coordinates, with exact rational action. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def projection : Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C) →*
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex (Source.TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)).symm).comp
    ((Finite.SymplecticRestriction.CM.restriction (Source.QuadraticConjugation.CM.Field.RealField E) 3).comp
      (FieldAction.CM.assembled E (OppositeCoordinates.CM.coordinates E C)))

theorem projection_coordinates
    (g : Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C))
    (x : (Fin 3 ⊕ Fin 3) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (Source.QuadraticConjugation.CM.Field.RealField E)) :
    (projection E C g).val *ᵥ Source.OrientedFiniteCoordinates.CM.coordinates E C x =
      Source.OrientedFiniteCoordinates.CM.coordinates E C
        ((FieldAction.CM.assembled E (OppositeCoordinates.CM.coordinates E C) g).val *ᵥ x) := by
  unfold projection Source.OrientedFiniteCoordinates.CM.coordinates
  change (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex
    (Source.TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)).symm
    (Finite.SymplecticRestriction.CM.restriction (Source.QuadraticConjugation.CM.Field.RealField E) 3
      (FieldAction.CM.assembled E (OppositeCoordinates.CM.coordinates E C) g))).val *ᵥ _ = _
  rw [RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex_action]
  exact congrArg
    (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex
      ((Source.TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)).symm.sumCongr
        (Source.TraceFrame.CM.indexEquiv E (OppositeCoordinates.CM.coordinates E C)).symm))
    (Finite.SymplecticRestriction.CM.restriction_apply (Source.QuadraticConjugation.CM.Field.RealField E) 3
      (FieldAction.CM.assembled E (OppositeCoordinates.CM.coordinates E C) g) x)

theorem rational_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    (projection E C
      (Source.RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g)).val *ᵥ
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (Source.OrientedTraceFrame.CM.frame E C x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (Source.OrientedTraceFrame.CM.frame E C
        (Source.ComplexAction.CM.Symplectic.rationalAction E g x)) := by
  exact (congrArg
    (fun v => (projection E C
      (Source.RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g)).val *ᵥ v)
    (Source.OrientedFiniteCoordinates.CM.coordinates_rational E C x).symm).trans
    ((projection_coordinates E C _ _).trans
      ((congrArg (Source.OrientedFiniteCoordinates.CM.coordinates E C)
        (FieldAction.CM.finite_rational_action E
          (OppositeCoordinates.CM.coordinates E C) g x)).trans
            (Source.OrientedFiniteCoordinates.CM.coordinates_rational E C _)))

theorem rational_projection (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    projection E C
      (Source.RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
        (Source.OrientedTraceFrame.CM.matrix E C *
          Source.ComplexAction.CM.Symplectic.symplectic E C g *
          (Source.OrientedTraceFrame.CM.matrix E C)⁻¹) := by
  apply Subtype.ext
  exact Finite.MatrixRationalDetermination.CM.eq_map_of_frame
    (Source.OrientedTraceFrame.CM.frame E C) (Source.OrientedTraceFrame.CM.frame E C).surjective
    (Source.ComplexAction.CM.Symplectic.rationalAction E g) _ _
    (rational_action E C g) (Source.OrientedTraceFrame.CM.conjugated_source_action E C g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Projection.CM
