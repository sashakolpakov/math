import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ProductOpens

/-! # Functions Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange

noncomputable section

/-! Coordinate-ring pushouts on the inverse images of affine opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y P : Scheme.{u}}

theorem openInclusion_appTop_topIso (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact (X.presheaf.map_comp _ _).symm

theorem morphismRestrict_appTop_topIso (a : P ⟶ X) (U : X.Opens) :
    (a ∣_ U).appTop ≫ (a ⁻¹ᵁ U).topIso.hom = U.topIso.hom ≫ a.app U := by
  have h := Scheme.Hom.resLE_app_top a (U := U) (V := a ⁻¹ᵁ U) le_rfl
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at h
  have h' : (a ∣_ U).appTop = U.topIso.hom ≫
      a.appLE U (a ⁻¹ᵁ U) le_rfl ≫ (a ⁻¹ᵁ U).topIso.inv := h
  refine (congrArg (fun k : Γ(U.toScheme, ⊤) ⟶ Γ((a ⁻¹ᵁ U).toScheme, ⊤) =>
    k ≫ (a ⁻¹ᵁ U).topIso.hom) h').trans ?_
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE_eq_app]

theorem affineOpen_isPushout_functions [IsAffine S] [IsAffine Y]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (U : X.Opens) (hU : IsAffineOpen U) :
    IsPushout
      (f.appTop ≫ X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op)
      g.appTop (a.app U)
      (b.appTop ≫ P.presheaf.map (homOfLE (show a ⁻¹ᵁ U ≤ ⊤ from le_top)).op) := by
  let : IsAffine U.toScheme := hU
  have H' : IsPullback (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ b) (U.ι ≫ f) g :=
    ((isPullback_morphismRestrict a U).flip.paste_horiz H.flip).flip
  have h := isPushout_appTop_of_isPullback H'
  refine h.of_iso (Iso.refl _) U.topIso (Iso.refl _) (a ⁻¹ᵁ U).topIso ?_ ?_ ?_ ?_
  · simp only [Scheme.Hom.comp_appTop, Iso.refl_hom, Category.id_comp, Category.assoc,
      openInclusion_appTop_topIso]
  · simp
  · exact morphismRestrict_appTop_topIso a U
  · simp only [Scheme.Hom.comp_appTop, Iso.refl_hom, Category.id_comp, Category.assoc,
      openInclusion_appTop_topIso]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange
