import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Restriction Ring Pushout -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RestrictionRingPushout

noncomputable section

/-! Restriction between affine opens, whose inverse images are affine, gives an actual pushout square on rings of sections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem affineRestriction_isPushout {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hYU : IsAffineOpen (f ⁻¹ᵁ U)) :
    IsPushout (f.app U) (X.presheaf.map (homOfLE h).op)
      (Y.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op)
      (f.app V) := by
  let H : IsPullback (𝟙 Y) f f (𝟙 X) := IsPullback.of_horiz_isIso (by simp)
  have hpre : f ⁻¹ᵁ V = (𝟙 Y) ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ f ⁻¹ᵁ V := by
    rw [Scheme.Hom.id_preimage, inf_eq_right.mpr (fun _ hx => h hx)]
  have hi : IsIso (pushoutSection H h (le_refl (f ⁻¹ᵁ U)) hpre) :=
    isIso_pushoutSection_of_isAffineOpen H h (le_refl (f ⁻¹ᵁ U)) hpre hU hV hYU
  have hp := (isIso_pushoutSection_iff H h (le_refl (f ⁻¹ᵁ U)) hpre).mp hi
  change IsPushout (f.app U ≫ Y.presheaf.map (𝟙 _))
    (𝟙 _ ≫ X.presheaf.map (homOfLE h).op)
    (𝟙 _ ≫ Y.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => h hx)).op)
    (f.app V ≫ Y.presheaf.map (𝟙 _)) at hp
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] using hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RestrictionRingPushout
