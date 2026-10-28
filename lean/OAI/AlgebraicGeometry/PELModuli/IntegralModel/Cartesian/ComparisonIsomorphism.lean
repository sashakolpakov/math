import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Comparison Isomorphism -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.ComparisonIsomorphism

noncomputable section

/-! A comparison of two actual pullback diagrams is an isomorphism;
an isomorphic comparison also reflects the pullback property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasPullbacks C]
    {P P' X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    {a : P ⟶ X} {b : P ⟶ Y} {a' : P' ⟶ X} {b' : P' ⟶ Y}

theorem isIso_of_cartesian_comparison (h : IsPullback a b f g) (h' : IsPullback a' b' f g)
    (c : P ⟶ P') (ha : c ≫ a' = a) (hb : c ≫ b' = b) : IsIso c := by
  have he : c = h.isoPullback.hom ≫ h'.isoPullback.inv := by
    apply h'.hom_ext
    · rw [ha, Category.assoc, h'.isoPullback_inv_fst, h.isoPullback_hom_fst]
    · rw [hb, Category.assoc, h'.isoPullback_inv_snd, h.isoPullback_hom_snd]
  rw [he]
  infer_instance

omit [HasPullbacks C] in
theorem isPullback_of_isIso_comparison (h' : IsPullback a' b' f g)
    (c : P ⟶ P') [IsIso c] (ha : c ≫ a' = a) (hb : c ≫ b' = b) : IsPullback a b f g := by
  exact h'.of_iso' (asIso c) (Iso.refl X) (Iso.refl Y) (Iso.refl Z)
    (by simpa only [asIso_hom, Iso.refl_hom, Category.comp_id] using ha)
    (by simpa only [asIso_hom, Iso.refl_hom, Category.comp_id] using hb)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.ComparisonIsomorphism
