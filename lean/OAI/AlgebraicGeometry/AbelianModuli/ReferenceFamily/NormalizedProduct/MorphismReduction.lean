import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.EndomorphismReduction

/-! # Morphism Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.MorphismReduction

/-! A morphism transported through two normalized products reduces
to the constant morphism induced by its original special fiber. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C)
    (X Y : D) (e : X ≅ F.obj (G.obj X)) (d : Y ≅ F.obj (G.obj Y))

theorem normalizedProductMorphism_reduction
    (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) (hd : NormalizedDual.OpenProductData.NormalizesProductFiber F G n d) (u : X ⟶ Y) :
    G.map (e.inv ≫ u ≫ d.hom) = G.map (F.map (G.map u)) := by
  have hi : G.map e.inv = n.hom.app (G.obj X) :=
    congrArg Iso.inv (EndomorphismReduction.normalizedProduct_mapIso_eq F G n X e he)
  have hh : G.map d.hom = n.inv.app (G.obj Y) :=
    congrArg Iso.hom (EndomorphismReduction.normalizedProduct_mapIso_eq F G n Y d hd)
  rw [Functor.map_comp, Functor.map_comp, hi, hh]
  exact NatIso.naturality_2 n (G.map u)

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.MorphismReduction
