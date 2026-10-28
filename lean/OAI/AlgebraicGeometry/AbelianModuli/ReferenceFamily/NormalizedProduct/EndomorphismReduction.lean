import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Endomorphism Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.EndomorphismReduction

/-! Conjugating an actual endomorphism through a normalized product
has the same special-fiber map as the constant reduced endomorphism. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C)
    (X : D) (e : X ≅ F.obj (G.obj X))

theorem normalizedProduct_mapIso_eq (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) :
    G.mapIso e = (n.app (G.obj X)).symm := by
  apply Iso.ext
  apply (cancel_mono (n.hom.app (G.obj X))).mp
  exact he.trans (n.app (G.obj X)).inv_hom_id.symm

theorem normalizedProductEndomorphism_reduction (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) (u : X ⟶ X) :
    G.map (e.inv ≫ u ≫ e.hom) = G.map (F.map (G.map u)) := by
  have h := normalizedProduct_mapIso_eq F G n X e he
  have hh : G.map e.hom = n.inv.app (G.obj X) := congrArg Iso.hom h
  have hi : G.map e.inv = n.hom.app (G.obj X) := congrArg Iso.inv h
  rw [Functor.map_comp, Functor.map_comp, hi, hh]
  exact NatIso.naturality_2 n (G.map u)

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.EndomorphismReduction
