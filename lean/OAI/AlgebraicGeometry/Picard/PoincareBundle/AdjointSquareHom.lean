import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentRestriction

/-! # Adjoint Square Hom -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointSquareHom

noncomputable section

/-!
# Adjoint morphisms across a canonical base-change square
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor

universe u v

variable {C D E F : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E] [Category.{v} F]
  {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
  {G : C ⥤ E} {H : D ⥤ F}
  (a : L ⊣ R) (a' : L' ⊣ R') (α : G ⋙ L' ≅ L ⋙ H)

/-- The adjoint of a restricted pullback morphism is its restricted adjoint followed by the mate. -/
theorem homEquiv_restrict {N : C} {M : D} (φ : L.obj N ⟶ M) :
    a'.homEquiv (G.obj N) (H.obj M) (α.hom.app N ≫ H.map φ) =
      G.map (a.homEquiv N M φ) ≫ (DescentRestriction.rightMate a a' α).app M := by
  rw [a'.homEquiv_unit, DescentRestriction.unit_via_rightMate a a' α]
  simp only [Functor.map_comp, Category.assoc]
  erw [← R'.map_comp_assoc, Iso.inv_hom_id_app, R'.map_id, Category.id_comp,
    ← (DescentRestriction.rightMate a a' α).naturality φ, ← Category.assoc, ← G.map_comp,
    ← a.homEquiv_unit]
  rfl

/-- A further morphism on the restricted target transports through the right adjoint. -/
theorem homEquiv_restrict_comp {N : C} {M : D} {M' : F}
    (φ : L.obj N ⟶ M) (τ : H.obj M ⟶ M') :
    a'.homEquiv (G.obj N) M' ((α.hom.app N ≫ H.map φ) ≫ τ) =
      (G.map (a.homEquiv N M φ) ≫ (DescentRestriction.rightMate a a' α).app M) ≫ R'.map τ := by
  rw [a'.homEquiv_naturality_right, homEquiv_restrict a a' α]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointSquareHom
