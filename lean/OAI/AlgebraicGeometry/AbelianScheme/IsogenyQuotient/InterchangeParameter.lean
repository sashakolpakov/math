import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameters
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

/-! # Interchange Parameter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameter.Construction

/-! The four-coordinate interchange parameter inherits the required
properness, smoothness, and geometric connectedness from its factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} (G X : Over S)

local instance lineInterchangeParameter_smooth [Smooth G.hom] [Smooth X.hom] :
    Smooth (InterchangeParameters.Construction.lineInterchangeParameter G X).hom := by
  have : Smooth (G ⊗ G).hom := by dsimp; infer_instance
  have : Smooth (X ⊗ X).hom := by dsimp; infer_instance
  dsimp [InterchangeParameters.Construction.lineInterchangeParameter]
  infer_instance

local instance lineInterchangeParameter_proper [IsProper G.hom] [IsProper X.hom] :
    IsProper (InterchangeParameters.Construction.lineInterchangeParameter G X).hom := by
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : IsProper (X ⊗ X).hom := by dsimp; infer_instance
  dsimp [InterchangeParameters.Construction.lineInterchangeParameter]
  infer_instance

local instance lineInterchangeParameter_connected [Smooth G.hom] [Smooth X.hom]
    [GeometricallyConnected G.hom] [GeometricallyConnected X.hom] :
    GeometricallyConnected (InterchangeParameters.Construction.lineInterchangeParameter G X).hom := by
  have : Smooth (G ⊗ G).hom := by dsimp; infer_instance
  have : Smooth (X ⊗ X).hom := by dsimp; infer_instance
  have : GeometricallyConnected (G ⊗ G).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst G.hom G.hom) G.hom
  have : GeometricallyConnected (X ⊗ X).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst X.hom X.hom) X.hom
  exact GeometricallyConnected.comp
    (CategoryTheory.Limits.pullback.fst (G ⊗ G).hom (X ⊗ X).hom) (G ⊗ G).hom

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeParameter.Construction
