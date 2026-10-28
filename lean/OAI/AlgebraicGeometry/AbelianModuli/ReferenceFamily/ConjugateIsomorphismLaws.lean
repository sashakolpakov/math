import Mathlib.CategoryTheory.Iso

/-! # Conjugate Isomorphism Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConjugateIsomorphismLaws

/-! Conjugation preserves automorphism composition and is faithful. -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y)

theorem conjugateIso_refl :
    e.symm ≪≫ Iso.refl X ≪≫ e = Iso.refl Y := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.id_comp, e.inv_hom_id]

theorem conjugateIso_trans (f g : X ≅ X) :
    e.symm ≪≫ (f ≪≫ g) ≪≫ e = (e.symm ≪≫ f ≪≫ e) ≪≫ (e.symm ≪≫ g ≪≫ e) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

theorem conjugateIso_injective :
    Function.Injective (fun f : X ≅ X => e.symm ≪≫ f ≪≫ e) := by
  intro f g h
  have hh := congrArg (fun a : Y ≅ Y => a.hom) h
  change e.inv ≫ (f.hom ≫ e.hom) = e.inv ≫ (g.hom ≫ e.hom) at hh
  have hh' := (cancel_epi e.inv).mp hh
  exact Iso.ext ((cancel_mono e.hom).mp hh')

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConjugateIsomorphismLaws
