import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.SmoothAffineDualProduct

/-! # Open Product Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

noncomputable section

/-! An actual product isomorphism on an open subfamily, retaining
its ambient inclusion and its identity on the actual special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w z

def NormalizesProductFiber
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C)
    {X : D} (e : X ≅ F.obj (G.obj X)) : Prop :=
  G.map e.hom ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X)

structure NormalizedProductRestrictionData
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C)
    {U X : D} (i : U ⟶ X) (e : X ≅ F.obj (G.obj X)) where
  iso : U ≅ F.obj (G.obj U)
  commutes : iso.hom ≫ F.map (G.map i) = i ≫ e.hom
  normalized : NormalizesProductFiber F G n iso

def normalizedProductRestrictionOfReduction
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C)
    {U X : D} (i : U ⟶ X) (e : X ≅ F.obj (G.obj X))
    (f : U ≅ F.obj (G.obj U))
    (hf : f.hom ≫ F.map (G.map i) = i ≫ e.hom)
    (hr : G.map f.hom = (n.app (G.obj U)).inv) :
    NormalizedProductRestrictionData F G n i e := by
  refine ⟨f, hf, ?_⟩
  change G.map f.hom ≫ n.hom.app (G.obj U) = _
  rw [hr]
  exact (n.app (G.obj U)).inv_hom_id

abbrev NormalizesDualProductFiber (k : Type) [CommRing k]
    {X : Over (Spec (.of (DualNumber k)))}
    (e : X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj
      ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X)) :=
  NormalizesProductFiber (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k))
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k) e

abbrev NormalizedDualProductRestriction (k : Type) [CommRing k]
    {U X : Over (Spec (.of (DualNumber k)))} (i : U ⟶ X)
    (e : X ≅ (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k)).obj
      ((Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)).obj X)) :=
  NormalizedProductRestrictionData (Over.pullback (Smooth.AffineDualProduct.dualBaseProjection k))
    (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction k)) (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso k) i e

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData
