import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.MapComparison

/-! # Witness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Witness

/-! Exact recovery of a normalized product map equips its actual
isomorphism witness with the same normalization. -/

open _root_.CategoryTheory

attribute [local implicit_reducible] NormalizedDual.OpenProductData.NormalizesProductFiber

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (G : D ⥤ C)
    (n : F ⋙ G ≅ 𝟭 C) {X : D}

theorem normalizedProductIsoWitness_of_map (f : X ⟶ F.obj (G.obj X))
    (hf : G.map f ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X))
    (h : ∃ e : X ≅ F.obj (G.obj X), e.hom = f) :
    ∃ e : X ≅ F.obj (G.obj X), NormalizedDual.OpenProductData.NormalizesProductFiber F G n e ∧ e.hom = f := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, MapComparison.normalizedProductMap_map_congr F G n e.hom f he hf, he⟩

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Witness
