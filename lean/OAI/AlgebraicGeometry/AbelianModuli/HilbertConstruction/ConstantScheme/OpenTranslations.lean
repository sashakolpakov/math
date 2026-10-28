import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenFunctions

/-! # Open Translations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenTranslations

noncomputable section

/-! Constant-scheme translations restrict to every inverse-image open, and the actual open-set splitting preserves the translation action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (G : Type u) [Group G] (U : S.Opens)

theorem constantSchemeRightTranslation_preimage (a : G) :
    (Translations.constantSchemeRightTranslation S G a).left ⁻¹ᵁ ((Iff.constantScheme S G).hom ⁻¹ᵁ U) =
      (Iff.constantScheme S G).hom ⁻¹ᵁ U :=
  congrArg (fun f : (Iff.constantScheme S G).left ⟶ S => f ⁻¹ᵁ U)
    (Translations.constantSchemeRightTranslation S G a).w

def constantSchemeOpenTranslation (a : G) :
    ((Iff.constantScheme S G).hom ⁻¹ᵁ U).toScheme ⟶ ((Iff.constantScheme S G).hom ⁻¹ᵁ U).toScheme :=
  (Translations.constantSchemeRightTranslation S G a).left.resLE _ _
    (constantSchemeRightTranslation_preimage S G U a).symm.le

theorem constantSchemeOpenTranslation_inclusion (a : G) :
    constantSchemeOpenTranslation S G U a ≫ ((Iff.constantScheme S G).hom ⁻¹ᵁ U).ι =
      ((Iff.constantScheme S G).hom ⁻¹ᵁ U).ι ≫ (Translations.constantSchemeRightTranslation S G a).left :=
  Scheme.Hom.resLE_comp_ι _ _

theorem constantSchemeOpenIso_equivariant_inclusion (a : G) :
    (Translations.constantSchemeRightTranslation U.toScheme G a).left ≫ (OpenFunctions.constantSchemeOpenIso S G U).hom ≫
      ((Iff.constantScheme S G).hom ⁻¹ᵁ U).ι =
        (OpenFunctions.constantSchemeOpenIso S G U).hom ≫ ((Iff.constantScheme S G).hom ⁻¹ᵁ U).ι ≫
          (Translations.constantSchemeRightTranslation S G a).left := by
  apply Sigma.hom_ext
  intro i
  have hL : Sigma.ι (fun _ : G => U.toScheme) i ≫
      (Translations.constantSchemeRightTranslation U.toScheme G a).left ≫ (OpenFunctions.constantSchemeOpenIso S G U).hom ≫
        ((Iff.constantScheme S G).hom ⁻¹ᵁ U).ι = U.ι ≫ Sigma.ι (fun _ : G => S) (i * a) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (OpenFunctions.constantSchemeOpenIso S G U).hom ≫
        ((Iff.constantScheme S G).hom ⁻¹ᵁ U).ι)
        (Translations.constantSchemeRightTranslation_label U.toScheme G a i)).trans
          (OpenFunctions.constantSchemeOpenIso_label_inclusion S G U (i * a)))
  have hR : Sigma.ι (fun _ : G => U.toScheme) i ≫ (OpenFunctions.constantSchemeOpenIso S G U).hom ≫
      ((Iff.constantScheme S G).hom ⁻¹ᵁ U).ι ≫ (Translations.constantSchemeRightTranslation S G a).left =
        U.ι ≫ Sigma.ι (fun _ : G => S) (i * a) :=
    (Category.assoc _ _ _).symm.trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (Translations.constantSchemeRightTranslation S G a).left)
          (OpenFunctions.constantSchemeOpenIso_label_inclusion S G U i)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun k => U.ι ≫ k) (Translations.constantSchemeRightTranslation_label S G a i)))))
  exact hL.trans hR.symm

theorem constantSchemeOpenIso_equivariant (a : G) :
    (Translations.constantSchemeRightTranslation U.toScheme G a).left ≫ (OpenFunctions.constantSchemeOpenIso S G U).hom =
      (OpenFunctions.constantSchemeOpenIso S G U).hom ≫ constantSchemeOpenTranslation S G U a := by
  apply (cancel_mono ((Iff.constantScheme S G).hom ⁻¹ᵁ U).ι).mp
  exact (Category.assoc _ _ _).trans
    ((constantSchemeOpenIso_equivariant_inclusion S G U a).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => (OpenFunctions.constantSchemeOpenIso S G U).hom ≫ k)
          (constantSchemeOpenTranslation_inclusion S G U a))).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenTranslations
