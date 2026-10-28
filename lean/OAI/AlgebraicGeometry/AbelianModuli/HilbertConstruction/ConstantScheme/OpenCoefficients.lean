import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenFunctions

/-! # Open Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenCoefficients

noncomputable section

/-! The open-set constant-scheme coordinates respect the actual coefficient functions from the base open. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (I : Type u) (U : S.Opens)

theorem constantSchemeOpenIso_over :
    (OpenFunctions.constantSchemeOpenIso S I U).hom ≫ ((Iff.constantScheme S I).hom ∣_ U) =
      (Iff.constantScheme U.toScheme I).hom :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => (Constant.BaseChange.constantSchemeBaseChangeIso U.ι I).hom.left ≫ k)
      (isPullback_morphismRestrict (Iff.constantScheme S I).hom U).flip.isoPullback_inv_snd).trans
        (Constant.BaseChange.constantSchemeBaseChangeIso U.ι I).hom.w)

theorem morphismRestrict_appTop_coefficient {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) :
    f.app V ≫ (f ⁻¹ᵁ V).topIso.inv = V.topIso.inv ≫ (f ∣_ V).appTop := by
  have h := (arrowResLEAppIso f V (f ⁻¹ᵁ V) le_rfl).inv.w.symm
  change f.appLE V (f ⁻¹ᵁ V) le_rfl ≫ (f ⁻¹ᵁ V).topIso.inv =
    V.topIso.inv ≫ (f.resLE V (f ⁻¹ᵁ V) le_rfl).appTop at h
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.resLE_eq_morphismRestrict] at h
  exact h

theorem constantSchemeOpenRingIso_structure (r : Γ(S, U)) (i : I) :
    (OpenFunctions.constantSchemeOpenRingIso S I U).hom ((Iff.constantScheme S I).hom.app U r) i = U.topIso.inv r := by
  let p := (Iff.constantScheme S I).hom
  let e := OpenFunctions.constantSchemeOpenIso S I U
  have he : (p ∣_ U).appTop ≫ e.hom.appTop = (Iff.constantScheme U.toScheme I).hom.appTop :=
    (Scheme.Hom.comp_appTop _ _).symm.trans
      (congrArg (fun f : (Iff.constantScheme U.toScheme I).left ⟶ U.toScheme => f.appTop)
        (constantSchemeOpenIso_over S I U))
  have hc : p.app U ≫ (p ⁻¹ᵁ U).topIso.inv ≫ e.hom.appTop =
      U.topIso.inv ≫ (Iff.constantScheme U.toScheme I).hom.appTop :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ e.hom.appTop) (morphismRestrict_appTop_coefficient p U)).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => U.topIso.inv ≫ k) he)))
  exact (congrArg (fun z : Γ((Iff.constantScheme U.toScheme I).left, ⊤) =>
    (GlobalFunctions.constantSchemeGlobalRingIso U.toScheme I).hom z i) (ConcreteCategory.congr_hom hc r)).trans
      (FunctionCoordinates.constantSchemeGlobalRingIso_structure U.toScheme I (U.topIso.inv r) i)

def constantSchemeSectionRingEquiv :
    Γ((Iff.constantScheme S I).left, (Iff.constantScheme S I).hom ⁻¹ᵁ U) ≃+* (I → Γ(S, U)) :=
  (OpenFunctions.constantSchemeOpenRingIso S I U).commRingCatIsoToRingEquiv.trans
    (RingEquiv.piCongrRight (fun _ : I => U.topIso.commRingCatIsoToRingEquiv))

theorem constantSchemeSectionRingEquiv_structure (r : Γ(S, U)) (i : I) :
    constantSchemeSectionRingEquiv S I U ((Iff.constantScheme S I).hom.app U r) i = r :=
  (congrArg (fun z => U.topIso.hom z) (constantSchemeOpenRingIso_structure S I U r i)).trans
    (ConcreteCategory.congr_hom U.topIso.inv_hom_id r)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenCoefficients
