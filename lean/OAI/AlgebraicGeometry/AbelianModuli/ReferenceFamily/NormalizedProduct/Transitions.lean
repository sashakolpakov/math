import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.FiberNormalization

/-! # Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Transitions

noncomputable section

/-! The difference between normalized product charts acts identically
on the actual special fiber, before choosing ring coordinates. -/

open _root_.CategoryTheory

universe u v w z

theorem normalized_product_transition_fiber
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C) (X : D)
    (e f : X ≅ F.obj (G.obj X))
    (he : G.map e.hom ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X))
    (hf : G.map f.hom ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X)) :
    G.map (e.inv ≫ f.hom) = 𝟙 (G.obj (F.obj (G.obj X))) := by
  apply (cancel_mono (n.hom.app (G.obj X))).mp
  rw [G.map_comp, Category.assoc, hf, Category.comp_id, Category.id_comp]
  calc
    G.map e.inv = G.map e.inv ≫ (G.map e.hom ≫ n.hom.app (G.obj X)) := by
      rw [he, Category.comp_id]
    _ = n.hom.app (G.obj X) := by
      rw [← Category.assoc, ← G.map_comp, e.inv_hom_id, G.map_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Transitions
