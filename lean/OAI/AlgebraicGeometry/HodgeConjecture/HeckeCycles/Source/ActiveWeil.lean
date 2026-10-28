import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveMetaplectic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexBare
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData

/-! # Active Weil -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveWeil.CM

noncomputable section

/-! Place the source's actual active metaplectic action in the finite
group of its fully constructed Weil data, with exact operators and projection. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def lift : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] →* WeilData.CM.FiniteCoverGroup E places :=
  (WeilReindexBare.CM.lift (GeometricSource.CM.Positions E places)).comp (ActiveMetaplectic.CM.lift E C f)

theorem action (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    (WeilData.CM.weilData E places).finite.action (lift E C f g) φ =
      TraceAction.CM.productAction E (OppositeCoordinates.CM.coordinates E C) f (g, 1) φ :=
  (WeilReindexBare.CM.action (GeometricSource.CM.Positions E places) (ActiveMetaplectic.CM.lift E C f g) φ).trans
    (congrArg (fun T => T φ) (ActiveMetaplectic.CM.action E C f g))

theorem projection_matrix (g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) :
    ((WeilData.CM.weilData E places).finite.project (lift E C f g)).val =
      (SourceFinite.Projection.CM.projection E C (ActiveMetaplectic.CM.inclusion E C f g)).val :=
  (WeilReindexBare.CM.projection_matrix (GeometricSource.CM.Positions E places) (ActiveMetaplectic.CM.lift E C f g)).trans
    (ActiveMetaplectic.CM.projection_matrix E C f g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveWeil.CM
