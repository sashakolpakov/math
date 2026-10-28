import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Oscillator
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialLinearOscillatorLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Topology

/-! # Active Metaplectic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveMetaplectic.CM

noncomputable section

/-! The actual distinguished SL3(Q_q) action has a homomorphic lift
to the intrinsic finite metaplectic group, with its exact source operator. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def inclusion : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] →*
    SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E C) :=
  (SourceFinite.Product.CM.equivalence E (OppositeCoordinates.CM.coordinates E C) f).toMonoidHom.comp
    (MonoidHom.inl _ _)

def oscillator : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] →*
    Finite.FiniteOscillator.CM.Oscillator (I := GeometricSource.CM.Positions E places) :=
  (SourceFinite.Oscillator.CM.lift E C).comp (inclusion E C f)

def lift : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] →*
    Finite.BareNe.CM.Group.BareGroup (I := GeometricSource.CM.Positions E places) :=
  SpecialLinearOscillatorLift.CM.lift (oscillator E C f)

theorem projection_matrix (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    (Finite.BareNe.CM.Group.bareProjection (lift E C f g)).val =
      (SourceFinite.Projection.CM.projection E C (inclusion E C f g)).val :=
  SourceFinite.Oscillator.CM.projection_matrix E C (inclusion E C f g)

theorem action (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    Finite.BareNe.CM.Group.bareAction (lift E C f g) =
      TraceAction.CM.productAction E (OppositeCoordinates.CM.coordinates E C) f (g, 1) := rfl

theorem smooth (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    IsOpen {g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] |
      Finite.BareNe.CM.Group.bareAction (lift E C f g) φ = φ} :=
  (TraceAction.CM.product_smooth E (OppositeCoordinates.CM.coordinates E C) f φ).preimage
    (continuous_id.prodMk continuous_const)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveMetaplectic.CM
