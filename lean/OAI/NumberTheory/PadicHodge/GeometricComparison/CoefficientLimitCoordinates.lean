import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientLimit

/-! # Coefficient Limit Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientLimitCoordinates.CoefficientLimitSourceCoordinates

noncomputable section

/-! Limit comparison coordinates after a given isomorphism from the
original integral source into its inverse limit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe uJ vJ uC vC uD vD
variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  (P : J ⥤ C) (Q : J ⥤ D) (G : C ⥤ D)
  [HasLimit P] [HasLimitsOfShape J D] [PreservesLimit P G]
  (e : P ⋙ G ≅ Q) {M : C} (s : M ≅ limit P)

def iso : G.obj M ≅ limit Q := G.mapIso s ≪≫ CoefficientLimit.CoefficientLimitComparison.iso P Q G e

theorem hom_π (j : J) : (iso P Q G e s).hom ≫ limit.π Q j =
    G.map (s.hom ≫ limit.π P j) ≫ e.hom.app j := by
  change (G.map s.hom ≫ (CoefficientLimit.CoefficientLimitComparison.iso P Q G e).hom) ≫ limit.π Q j = _
  rw [Category.assoc, CoefficientLimit.CoefficientLimitComparison.hom_π, ← Category.assoc, ← G.map_comp]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientLimitCoordinates.CoefficientLimitSourceCoordinates
