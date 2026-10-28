import Mathlib.CategoryTheory.NatIso

/-! # Reduction Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.ReductionIso

/-! A product map normalized by an actual fiber comparison induces
an isomorphism on the special fiber. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (G : D ⥤ C)
    (n : F ⋙ G ≅ 𝟭 C) {X : D}

theorem normalizedProductMap_reduction_isIso (f : X ⟶ F.obj (G.obj X))
    (hf : G.map f ≫ n.hom.app (G.obj X) = 𝟙 (G.obj X)) : IsIso (G.map f) := by
  have hm : G.map f = (n.app (G.obj X)).inv :=
    (cancel_mono (n.app (G.obj X)).hom).mp (hf.trans (n.app (G.obj X)).inv_hom_id.symm)
  exact hm.symm ▸ (inferInstance : IsIso (n.app (G.obj X)).inv)

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.ReductionIso
