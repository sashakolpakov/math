import Mathlib.CategoryTheory.EqToHom

/-! # Transported Iso Square -/

namespace OAI.CategoryTheory.Isomorphisms.TransportedIsoSquare

noncomputable section

open _root_.CategoryTheory
universe u v
theorem transportedIsoSquare {C : Type u} [Category.{v} C]
    {A A' B B' : C} (hA : A' = A) (hB : B' = B) (e : A ≅ B)
    (a : A ⟶ A) (a' : A' ⟶ A') (b : B ⟶ B) (b' : B' ⟶ B')
    (ha : a' ≫ eqToHom hA = eqToHom hA ≫ a)
    (hb : b' ≫ eqToHom hB = eqToHom hB ≫ b)
    (h : a ≫ e.hom = e.hom ≫ b) :
    a' ≫ (eqToIso hA ≪≫ e ≪≫ (eqToIso hB).symm).hom =
      (eqToIso hA ≪≫ e ≪≫ (eqToIso hB).symm).hom ≫ b' := by
  cases hA
  cases hB
  simpa only [eqToHom_refl, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    Iso.symm_hom, Iso.refl_inv, Category.comp_id, Category.id_comp] using
    (show a' ≫ e.hom = e.hom ≫ b' from by
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at ha hb
      rw [ha, hb]
      exact h)

end

end OAI.CategoryTheory.Isomorphisms.TransportedIsoSquare
