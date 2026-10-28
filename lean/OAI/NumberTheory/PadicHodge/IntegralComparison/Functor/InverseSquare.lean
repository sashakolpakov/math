import Mathlib.CategoryTheory.Equivalence

/-! # Inverse Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.InverseSquare

noncomputable section

/-! Inverse comparison maps retain an exact commuting functor square. -/
open _root_.CategoryTheory
variable {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
  {A B : C} {A' B' : D} (eA : G.obj A ≅ A') (eB : G.obj B ≅ B')
  (f : A ⟶ B) (f' : A' ⟶ B')
  (h : G.map f ≫ eB.hom = eA.hom ≫ f')

include h in
theorem isIso [IsIso f] : IsIso f' := by
  have he : f' = eA.inv ≫ G.map f ≫ eB.hom := by
    apply (cancel_epi eA.hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.symm
  rw [he]
  infer_instance

include h in
theorem inverse [IsIso f] [IsIso f'] :
    G.map (inv f) ≫ eA.hom = eB.hom ≫ inv f' := by
  apply (cancel_mono f').mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, ← G.map_comp, IsIso.inv_hom_id, G.map_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.InverseSquare
