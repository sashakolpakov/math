import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Gauge -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Gauge

/-! An automorphism fixing the actual fiber preserves a product
chart's normalization. Commuting gauges preserve restriction squares. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (G : D ⥤ C)
    (n : F ⋙ G ≅ 𝟭 C) {X : D}

theorem normalizesProductFiber_postcomp (e : X ≅ F.obj (G.obj X))
    (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e)
    (g : F.obj (G.obj X) ≅ F.obj (G.obj X)) (hg : G.map g.hom = 𝟙 _) :
    NormalizedDual.OpenProductData.NormalizesProductFiber F G n (e ≪≫ g) := by
  change G.map (e.hom ≫ g.hom) ≫ n.hom.app (G.obj X) = 𝟙 _
  rw [G.map_comp, hg, Category.comp_id]
  exact he

theorem productChartGauge_restriction_square {U V A B : D} (i : U ⟶ V) (j : A ⟶ B)
    (e : U ≅ A) (f : V ≅ B) (a : A ≅ A) (b : B ≅ B)
    (he : e.hom ≫ j = i ≫ f.hom) (ha : a.hom ≫ j = j ≫ b.hom) :
    (e ≪≫ a).hom ≫ j = i ≫ (f ≪≫ b).hom := by
  change (e.hom ≫ a.hom) ≫ j = i ≫ (f.hom ≫ b.hom)
  rw [Category.assoc, ha, ← Category.assoc, he, Category.assoc]

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Gauge
