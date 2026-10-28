import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenTranslations

/-! # Open Function Translation Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.OpenFunctionTranslationValues

noncomputable section

/-! The action on the actual sections over an inverse-image open is right translation in the constructed label coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (G : Type u) [Group G] (U : S.Opens)

theorem constantSchemeOpenRingIso_translate (a : G)
    (s : Γ((ConstantScheme.Iff.constantScheme S G).left, (ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U)) (i : G) :
    (ConstantScheme.OpenFunctions.constantSchemeOpenRingIso S G U).hom
        ((ConstantScheme.Translations.constantSchemeRightTranslation S G a).left.appLE
          ((ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U) ((ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U)
          (ConstantScheme.OpenTranslations.constantSchemeRightTranslation_preimage S G U a).symm.le s) i =
      (ConstantScheme.OpenFunctions.constantSchemeOpenRingIso S G U).hom s (i * a) := by
  let V := (ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U
  let t := (ConstantScheme.Translations.constantSchemeRightTranslation S G a).left
  let q := ConstantScheme.OpenTranslations.constantSchemeOpenTranslation S G U a
  let e := ConstantScheme.OpenFunctions.constantSchemeOpenIso S G U
  let h := (ConstantScheme.OpenTranslations.constantSchemeRightTranslation_preimage S G U a).symm.le
  have hr : t.appLE V V h ≫ V.topIso.inv = V.topIso.inv ≫ q.appTop :=
    (arrowResLEAppIso t V V h).inv.w.symm
  have he : q.appTop ≫ e.hom.appTop =
      e.hom.appTop ≫ (ConstantScheme.Translations.constantSchemeRightTranslation U.toScheme G a).left.appTop :=
    (congrArg (fun f : (ConstantScheme.Iff.constantScheme U.toScheme G).left ⟶ V.toScheme => f.appTop)
      (ConstantScheme.OpenTranslations.constantSchemeOpenIso_equivariant S G U a)).symm
  have hc : t.appLE V V h ≫ V.topIso.inv ≫ e.hom.appTop =
      V.topIso.inv ≫ e.hom.appTop ≫ (ConstantScheme.Translations.constantSchemeRightTranslation U.toScheme G a).left.appTop :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ e.hom.appTop) hr).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => V.topIso.inv ≫ k) he)))
  exact (congrArg (fun z : Γ((ConstantScheme.Iff.constantScheme U.toScheme G).left, ⊤) =>
    (ConstantScheme.GlobalFunctions.constantSchemeGlobalRingIso U.toScheme G).hom z i)
    (ConcreteCategory.congr_hom hc s)).trans
      (ConstantScheme.FunctionCoordinates.constantSchemeGlobalRingIso_translate U.toScheme G a (e.hom.appTop (V.topIso.inv s)) i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.OpenFunctionTranslationValues
