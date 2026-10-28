import Mathlib.CategoryTheory.Yoneda

/-! # Representing Iso Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentingIsoPoints

noncomputable section

/-! The canonical isomorphism between two representing objects preserves every represented point. -/

open _root_.CategoryTheory

universe u v

theorem representingIso_homEquiv {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type v}
    {X Y : C} (e : F.RepresentableBy X) (d : F.RepresentableBy Y) {T : C} (p : T ⟶ X) :
    d.homEquiv (p ≫ (e.uniqueUpToIso d).hom) = e.homEquiv p := by
  have h : (e.uniqueUpToIso d).hom = d.homEquiv.symm (e.homEquiv (𝟙 X)) := rfl
  rw [h, d.homEquiv_comp, Equiv.apply_symm_apply]
  exact (e.homEquiv_eq p).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentingIsoPoints
