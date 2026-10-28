import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Product
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChangeLabels

/-! # Product Labels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.ProductLabels

noncomputable section

/-! Each component of the constant-product isomorphism is the graph of its labeled constant section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {S : Scheme.{u}} (X : Over S) (I : Type u)

theorem constantSchemeProductIso_snd :
    (ConstantScheme.Product.constantSchemeProductIso X I).hom ≫ Limits.pullback.snd X.hom (ConstantScheme.Iff.constantScheme S I).hom =
      (BaseChange.constantSchemeBaseChangeIso X.hom I).hom.left ≫
        Limits.pullback.fst (ConstantScheme.Iff.constantScheme S I).hom X.hom := by
  change ((BaseChange.constantSchemeBaseChangeIso X.hom I).hom.left ≫
    (Limits.pullbackSymmetry (ConstantScheme.Iff.constantScheme S I).hom X.hom).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans (congrArg
    (fun k => (BaseChange.constantSchemeBaseChangeIso X.hom I).hom.left ≫ k)
    (Limits.pullbackSymmetry_hom_comp_snd (ConstantScheme.Iff.constantScheme S I).hom X.hom))

theorem constantSchemeProductIso_label_snd (i : I) :
    Limits.Sigma.ι (fun _ : I => X.left) i ≫ (ConstantScheme.Product.constantSchemeProductIso X I).hom ≫
      Limits.pullback.snd X.hom (ConstantScheme.Iff.constantScheme S I).hom =
        X.hom ≫ Limits.Sigma.ι (fun _ : I => S) i := by
  exact (congrArg (fun k => Limits.Sigma.ι (fun _ : I => X.left) i ≫ k)
    (constantSchemeProductIso_snd X I)).trans
      ((Category.assoc _ _ _).symm.trans (BaseChangeLabels.constantSchemeBaseChangeIso_label_fst X.hom I i))

def constantProductLabel (i : I) : X ⟶ X ⊗ ConstantScheme.Iff.constantScheme S I :=
  lift (𝟙 X) (toUnit X ≫ ConstantScheme.Morphisms.constantSchemeLabelPoint S I i)

theorem constantSchemeProductIso_label (i : I) :
    Limits.Sigma.ι (fun _ : I => X.left) i ≫ (ConstantScheme.Product.constantSchemeProductIso X I).hom =
      (constantProductLabel X I i).left := by
  apply Limits.pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => Limits.Sigma.ι (fun _ : I => X.left) i ≫ k)
        (ConstantScheme.Product.constantSchemeProductIso_fst X I)).trans
        ((ConstantScheme.Iff.constantScheme_ι_hom i).trans
          (congrArg (fun k : X ⟶ X => k.left)
            (lift_fst (𝟙 X) (toUnit X ≫ ConstantScheme.Morphisms.constantSchemeLabelPoint S I i))).symm))
  · exact (Category.assoc _ _ _).trans
      ((constantSchemeProductIso_label_snd X I i).trans
        (congrArg (fun k : X ⟶ ConstantScheme.Iff.constantScheme S I => k.left)
          (lift_snd (𝟙 X) (toUnit X ≫ ConstantScheme.Morphisms.constantSchemeLabelPoint S I i))).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.ProductLabels
