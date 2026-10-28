import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Local Triangle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.LocalTriangle

/-! The normalization of a local product chart gives the corresponding
triangle identity for any global map restricting to that chart. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (G : D ⥤ C)
    (n : F ⋙ G ≅ 𝟭 C) {U X : D}

theorem normalizedProduct_local_triangle (i : U ⟶ X) (e : U ≅ F.obj (G.obj U))
    (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) (f : X ⟶ F.obj (G.obj X))
    (hf : i ≫ f = e.hom ≫ F.map (G.map i)) :
    G.map i ≫ (G.map f ≫ n.hom.app (G.obj X)) = G.map i := by
  have hn : G.map (F.map (G.map i)) ≫ n.hom.app (G.obj X) =
      n.hom.app (G.obj U) ≫ G.map i := n.hom.naturality (G.map i)
  change G.map e.hom ≫ n.hom.app (G.obj U) = 𝟙 _ at he
  calc
    G.map i ≫ (G.map f ≫ n.hom.app (G.obj X)) = G.map (i ≫ f) ≫ n.hom.app (G.obj X) := by
      rw [G.map_comp, Category.assoc]
    _ = G.map (e.hom ≫ F.map (G.map i)) ≫ n.hom.app (G.obj X) := by rw [hf]
    _ = G.map e.hom ≫ (G.map (F.map (G.map i)) ≫ n.hom.app (G.obj X)) := by
      rw [G.map_comp, Category.assoc]
    _ = G.map e.hom ≫ (n.hom.app (G.obj U) ≫ G.map i) := by rw [hn]
    _ = G.map i := by rw [← Category.assoc, he, Category.id_comp]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.LocalTriangle
