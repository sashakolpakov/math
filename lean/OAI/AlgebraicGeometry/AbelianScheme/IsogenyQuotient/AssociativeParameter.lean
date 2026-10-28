import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameters
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

/-! # Associative Parameter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameter.Construction

/-! The associativity parameter inherits properness, smoothness,
and geometric connectedness from its two original factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} (G X : Over S)

local instance lineAssociativeParameter_smooth [Smooth G.hom] [Smooth X.hom] :
    Smooth (AssociativeParameters.Construction.lineAssociativeParameter G X).hom := by
  have : Smooth (G ⊗ G).hom := by dsimp; infer_instance
  have : Smooth ((G ⊗ G) ⊗ G).hom := by dsimp; infer_instance
  dsimp [AssociativeParameters.Construction.lineAssociativeParameter]
  infer_instance

local instance lineAssociativeParameter_proper [IsProper G.hom] [IsProper X.hom] :
    IsProper (AssociativeParameters.Construction.lineAssociativeParameter G X).hom := by
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : IsProper ((G ⊗ G) ⊗ G).hom := by dsimp; infer_instance
  dsimp [AssociativeParameters.Construction.lineAssociativeParameter]
  infer_instance

local instance lineAssociativeParameter_connected [Smooth G.hom] [Smooth X.hom]
    [GeometricallyConnected G.hom] [GeometricallyConnected X.hom] :
    GeometricallyConnected (AssociativeParameters.Construction.lineAssociativeParameter G X).hom := by
  have : Smooth (G ⊗ G).hom := by dsimp; infer_instance
  have : Smooth ((G ⊗ G) ⊗ G).hom := by dsimp; infer_instance
  have : GeometricallyConnected (G ⊗ G).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst G.hom G.hom) G.hom
  have : GeometricallyConnected ((G ⊗ G) ⊗ G).hom :=
    GeometricallyConnected.comp (CategoryTheory.Limits.pullback.fst (G ⊗ G).hom G.hom) (G ⊗ G).hom
  exact GeometricallyConnected.comp
    (CategoryTheory.Limits.pullback.fst ((G ⊗ G) ⊗ G).hom X.hom) ((G ⊗ G) ⊗ G).hom

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AssociativeParameter.Construction
