import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.PushforwardFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Translations

/-! # Structure Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureRepresentation

noncomputable section

/-! The constant torsor acts on its actual pushed-forward structure sheaf by pullback of regular functions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (G : Type u) [Group G]

def constantStructurePushforward : S.Modules :=
  (Structure.PushforwardFunctor.structurePushforwardFunctor S).obj (.op (ConstantScheme.Iff.constantScheme S G))

def constantStructureRepresentation : G →* End (constantStructurePushforward S G) where
  toFun a := (Structure.PushforwardFunctor.structurePushforwardFunctor S).map (ConstantScheme.Translations.constantSchemeRightTranslation S G a).op
  map_one' := by
    change (Structure.PushforwardFunctor.structurePushforwardFunctor S).map (ConstantScheme.Translations.constantSchemeRightTranslation S G 1).op = 𝟙 _
    rw [ConstantScheme.Translations.constantSchemeRightTranslation_one]
    exact (Structure.PushforwardFunctor.structurePushforwardFunctor S).map_id _
  map_mul' a b := by
    change (Structure.PushforwardFunctor.structurePushforwardFunctor S).map (ConstantScheme.Translations.constantSchemeRightTranslation S G (a * b)).op =
      (Structure.PushforwardFunctor.structurePushforwardFunctor S).map (ConstantScheme.Translations.constantSchemeRightTranslation S G b).op ≫
        (Structure.PushforwardFunctor.structurePushforwardFunctor S).map (ConstantScheme.Translations.constantSchemeRightTranslation S G a).op
    rw [← ConstantScheme.Translations.constantSchemeRightTranslation_comp S G a b]
    exact (Structure.PushforwardFunctor.structurePushforwardFunctor S).map_comp _ _

theorem constantStructureRepresentation_app (a : G) (U : S.Opens)
    (s : Γ((ConstantScheme.Iff.constantScheme S G).left, (ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U)) :
    (constantStructureRepresentation S G a).app U s =
      (ConstantScheme.Translations.constantSchemeRightTranslation S G a).left.appLE
        ((ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U) ((ConstantScheme.Iff.constantScheme S G).hom ⁻¹ᵁ U)
        (Structure.PushforwardMorphism.overMorphism_preimage_le _ _ _ (ConstantScheme.Translations.constantSchemeRightTranslation S G a).w U) s :=
  Structure.PushforwardMorphism.structurePushforwardOverMorphism_app _ _ _ (ConstantScheme.Translations.constantSchemeRightTranslation S G a).w U s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.StructureRepresentation
