import OAI.AlgebraicGeometry.Resolution.Blowups.EmbeddedStrictTransform

/-! # Protected Open Lift Uniqueness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedOpenLiftUniqueness.Construction

noncomputable section

/-! Maps over an open where the ambient morphism is an isomorphism are the canonical strict-open lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem eq_protected_open_lift_of_over
    {Z Y X : Scheme.{u}} (π : Y ⟶ X) (O : X.Opens) [IsIso (π ∣_ O)]
    (i : Z ⟶ O.toScheme) (q : Z ⟶ Y) (hq : q ≫ π = i ≫ O.ι) :
    q = (i ≫ inv (π ∣_ O)) ≫ (π ⁻¹ᵁ O).ι := by
  let H := isPullback_morphismRestrict π O
  let a := H.lift i q hq.symm
  have ha : a ≫ (π ∣_ O) = i := H.lift_fst i q hq.symm
  have hb : a ≫ (π ⁻¹ᵁ O).ι = q := H.lift_snd i q hq.symm
  have he : a = i ≫ inv (π ∣_ O) := (IsIso.eq_comp_inv (π ∣_ O)).mpr ha
  rw [← hb, he]

theorem eq_embeddedStrictOpenMap_of_over
    {Z Y X : Scheme.{u}} (π : Y ⟶ X) (i : Z ⟶ X) (O : X.Opens) [IsIso (π ∣_ O)]
    (q : (i ⁻¹ᵁ O).toScheme ⟶ Y) (hq : q ≫ π = (i ⁻¹ᵁ O).ι ≫ i) :
    q = EmbeddedStrictTransform.Construction.embeddedStrictOpenMap π i O := by
  exact eq_protected_open_lift_of_over π O (i ∣_ O) q (hq.trans (morphismRestrict_ι i O).symm)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedOpenLiftUniqueness.Construction
