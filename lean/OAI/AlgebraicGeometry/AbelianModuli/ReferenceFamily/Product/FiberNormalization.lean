import Mathlib.CategoryTheory.NatIso

/-! # Fiber Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.FiberNormalization

noncomputable section

/-! Product identifications can be normalized along a retraction of
base-change functors using their induced automorphism of the fiber. -/

open _root_.CategoryTheory

universe u v w z

theorem exists_product_iso_identity_on_fiber
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) (G : D ⥤ C) (n : F ⋙ G ≅ 𝟭 C) (X : D)
    (h : Nonempty (X ≅ F.obj (G.obj X))) :
    ∃ e : X ≅ F.obj (G.obj X), G.map e.hom ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X) := by
  obtain ⟨e⟩ := h
  let a : G.obj X ≅ G.obj X := G.mapIso e ≪≫ n.app (G.obj X)
  let f := e ≪≫ F.mapIso a.symm
  refine ⟨f, ?_⟩
  change G.map (e.hom ≫ F.map a.inv) ≫ n.hom.app (G.obj X) = _
  rw [G.map_comp, Category.assoc]
  have hn : G.map (F.map a.inv) ≫ n.hom.app (G.obj X) =
      n.hom.app (G.obj X) ≫ a.inv := n.hom.naturality a.inv
  rw [hn, ← Category.assoc]
  change a.hom ≫ a.inv = _
  exact a.hom_inv_id

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.FiberNormalization
