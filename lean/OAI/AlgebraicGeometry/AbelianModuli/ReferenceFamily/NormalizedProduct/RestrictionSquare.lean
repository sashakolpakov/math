import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Transitions

/-! # Restriction Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.RestrictionSquare

noncomputable section

/-! Normalization gives the exact reduction square needed to restrict
a product chart to an open subfamily. -/

open _root_.CategoryTheory

universe u v w z

theorem normalized_product_restriction_square
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C)
    {U X : D} (i : U ⟶ X) (e : X ≅ F.obj (G.obj X))
    (he : G.map e.hom ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X)) :
    G.map (i ≫ e.hom) = (n.app (G.obj U)).inv ≫ G.map (F.map (G.map i)) := by
  have hi : G.map e.hom = (n.app (G.obj X)).inv := by
    apply (cancel_mono (n.hom.app (G.obj X))).mp
    exact he.trans (n.app (G.obj X)).inv_hom_id.symm
  rw [G.map_comp, hi]
  exact n.inv.naturality (G.map i)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.RestrictionSquare
