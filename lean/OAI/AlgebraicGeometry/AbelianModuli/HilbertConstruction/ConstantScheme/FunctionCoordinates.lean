import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.GlobalFunctions

/-! # Function Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.FunctionCoordinates

noncomputable section

/-! Constant-scheme function coordinates preserve the base coefficient algebra and turn actual geometric translation into right translation of functions. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (I : Type u)

theorem constantSchemeGlobalRingIso_apply (s : Γ((Iff.constantScheme S I).left, ⊤)) (i : I) :
    (GlobalFunctions.constantSchemeGlobalRingIso S I).hom s i = (Sigma.ι (fun _ : I => S) i).appTop s :=
  ConcreteCategory.congr_hom (GlobalFunctions.constantSchemeGlobalRingIso_projection S I i) s

theorem constantSchemeGlobalRingIso_structure (r : Γ(S, ⊤)) (i : I) :
    (GlobalFunctions.constantSchemeGlobalRingIso S I).hom ((Iff.constantScheme S I).hom.appTop r) i = r := by
  have h : (Iff.constantScheme S I).hom.appTop ≫ (Sigma.ι (fun _ : I => S) i).appTop = 𝟙 _ :=
    (Scheme.Hom.comp_appTop _ _).symm.trans
      ((congrArg (fun f : S ⟶ S => f.appTop) (Iff.constantScheme_ι_hom i)).trans Scheme.Hom.id_appTop)
  exact (constantSchemeGlobalRingIso_apply S I _ i).trans (ConcreteCategory.congr_hom h r)

abbrev constantSchemeGlobalAlgebra : Algebra Γ(S, ⊤) Γ((Iff.constantScheme S I).left, ⊤) :=
  (Iff.constantScheme S I).hom.appTop.hom.toAlgebra

attribute [local instance] constantSchemeGlobalAlgebra

def constantSchemeGlobalAlgEquiv : Γ((Iff.constantScheme S I).left, ⊤) ≃ₐ[Γ(S, ⊤)] (I → Γ(S, ⊤)) where
  __ := (GlobalFunctions.constantSchemeGlobalRingIso S I).commRingCatIsoToRingEquiv
  commutes' r := funext (constantSchemeGlobalRingIso_structure S I r)

variable (G : Type u) [Group G]

theorem constantSchemeGlobalRingIso_translate (a : G)
    (s : Γ((Iff.constantScheme S G).left, ⊤)) (i : G) :
    (GlobalFunctions.constantSchemeGlobalRingIso S G).hom ((Translations.constantSchemeRightTranslation S G a).left.appTop s) i =
      (GlobalFunctions.constantSchemeGlobalRingIso S G).hom s (i * a) := by
  have h : (Translations.constantSchemeRightTranslation S G a).left.appTop ≫ (Sigma.ι (fun _ : G => S) i).appTop =
      (Sigma.ι (fun _ : G => S) (i * a)).appTop :=
    (Scheme.Hom.comp_appTop _ _).symm.trans
      (congrArg (fun f : S ⟶ (Iff.constantScheme S G).left => f.appTop)
        (Translations.constantSchemeRightTranslation_label S G a i))
  exact (constantSchemeGlobalRingIso_apply S G _ i).trans
    ((ConcreteCategory.congr_hom h s).trans (constantSchemeGlobalRingIso_apply S G s (i * a)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.FunctionCoordinates
