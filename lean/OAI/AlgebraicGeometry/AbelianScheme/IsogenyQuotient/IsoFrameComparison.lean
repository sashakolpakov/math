import Mathlib.CategoryTheory.Iso

/-! # Iso Frame Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoFrameComparison.Construction

/-! Two normalized frames give the identity after identifying their
targets with their common fiber. -/

open _root_.CategoryTheory

theorem iso_frame_comparison_identity {C : Type*} [Category* C] {U X Y Z : C}
    (s : U ≅ X) (t : U ≅ Y) (a : X ≅ Z) (b : Y ≅ Z)
    (h : s ≪≫ a = t ≪≫ b) : a.symm ≪≫ (s.symm ≪≫ t) ≪≫ b = Iso.refl Z := by
  have he : a.symm ≪≫ (s.symm ≪≫ t) ≪≫ b = (s ≪≫ a).symm ≪≫ (t ≪≫ b) := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  rw [he, h, Iso.symm_self_id]

theorem iso_of_frame_square {C : Type*} [Category* C] {U X Y Z : C}
    (s : U ≅ X) (t : U ≅ Y) (a : X ≅ Z) (b : Y ≅ Z) (m : X ≅ Y)
    (hm : m ≪≫ b = a) (h : s ≪≫ a = t ≪≫ b) : m = s.symm ≪≫ t := by
  apply Iso.ext
  apply (cancel_epi s.hom).mp
  apply (cancel_mono b.hom).mp
  have he := congrArg Iso.hom ((congrArg (fun c => s ≪≫ c) hm).trans h)
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using he

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoFrameComparison.Construction
