import Mathlib.CategoryTheory.Linear.Basic

/-! # Inverse Hom -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.InverseHom.InverseHomCongr

noncomputable section

/-! Naturality of inverse coefficient-Hom transport along an actual commuting square of isomorphisms. -/

open _root_.CategoryTheory

variable {C : Type*} [Category* C]

theorem inverse_square {B D B' D' : C} (e : B ≅ D) (d : B' ≅ D')
    (a : B ⟶ B') (b : D ⟶ D') (h : e.hom ≫ b = a ≫ d.hom) :
    b ≫ d.inv = e.inv ≫ a := by
  rw [← cancel_epi e.hom, ← cancel_mono d.hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id] using h

variable (R : Type*) [CommRing R] [Preadditive C] [Linear R C]

theorem naturality {A B D B' D' : C} (e : B ≅ D) (d : B' ≅ D')
    (a : B ⟶ B') (b : D ⟶ D') (h : e.hom ≫ b = a ≫ d.hom) (x : A ⟶ D) :
    (Linear.homCongr R (Iso.refl A) d).symm (x ≫ b) =
      (Linear.homCongr R (Iso.refl A) e).symm x ≫ a := by
  simp only [Linear.homCongr_symm_apply, Iso.refl_hom, Category.id_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => x ≫ m) (inverse_square e d a b h)).trans (Category.assoc _ _ _).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.InverseHom.InverseHomCongr
