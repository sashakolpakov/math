import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Coefficient Limit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientLimit.CoefficientLimitComparison

noncomputable section

/-! Coordinates of the limit comparison obtained from a coefficient
functor and a natural isomorphism of the original diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe uJ vJ uC vC uD vD
variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  (P : J ⥤ C) (Q : J ⥤ D) (G : C ⥤ D)
  [HasLimit P] [HasLimitsOfShape J D] [PreservesLimit P G]
  (e : P ⋙ G ≅ Q)

def iso : G.obj (limit P) ≅ limit Q :=
  preservesLimitIso G P ≪≫ (lim (C := D)).mapIso e

theorem hom_π (j : J) : (iso P Q G e).hom ≫ limit.π Q j =
    G.map (limit.π P j) ≫ e.hom.app j := by
  change ((preservesLimitIso G P).hom ≫ limMap e.hom) ≫ limit.π Q j = _
  rw [Category.assoc, limMap_π, ← Category.assoc, preservesLimitIso_hom_π]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientLimit.CoefficientLimitComparison
