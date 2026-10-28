import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Existence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Existence

noncomputable section

/-! Package proved product existence in normalized chart data before
specializing the categorical operations to actual scheme base changes. -/

open _root_.CategoryTheory

universe u v w z

structure NormalizedProductChartData
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C) (X : D) where
  iso : X ≅ F.obj (G.obj X)
  normalized : NormalizedDual.OpenProductData.NormalizesProductFiber F G n iso

def normalizedProductChartOfExistence
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C) (X : D)
    (h : Nonempty (X ≅ F.obj (G.obj X))) :
    NormalizedProductChartData F G n X := by
  have hn := Product.FiberNormalization.exists_product_iso_identity_on_fiber F G n X h
  exact ⟨hn.choose, hn.choose_spec⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.Existence
