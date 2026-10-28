import Mathlib.CategoryTheory.NatIso

/-! # Functor Fixed Automorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FunctorFixedAutomorphisms

noncomputable section

/-! Changing coordinates preserves identity after applying the
special-fiber functor. -/

open _root_.CategoryTheory

universe u v w z

theorem functor_map_conjugate_identity
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) (f : X ≅ X)
    (h : F.map f.hom = 𝟙 (F.obj X)) :
    F.map (e.symm ≪≫ f ≪≫ e).hom = 𝟙 (F.obj Y) := by
  change F.map (e.inv ≫ (f.hom ≫ e.hom)) = _
  rw [F.map_comp, F.map_comp, h, Category.id_comp,
    ← F.map_comp, e.inv_hom_id, F.map_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FunctorFixedAutomorphisms
