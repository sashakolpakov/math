import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Morphisms

/-! # Translations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Translations

noncomputable section

/-! Right multiplication of labels defines actual translations of a constant scheme over its base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (G : Type u) [Group G]

def constantSchemeRightTranslation (a : G) : Iff.constantScheme S G ⟶ Iff.constantScheme S G :=
  Over.homMk (Sigma.desc (fun i : G => Sigma.ι (fun _ : G => S) (i * a))) (by
    apply Sigma.hom_ext
    intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (Iff.constantScheme S G).hom) (Sigma.ι_comp_desc _ i)).trans
        ((Iff.constantScheme_ι_hom (i * a)).trans (Iff.constantScheme_ι_hom i).symm)))

theorem constantSchemeRightTranslation_label (a i : G) :
    Sigma.ι (fun _ : G => S) i ≫ (constantSchemeRightTranslation S G a).left =
      Sigma.ι (fun _ : G => S) (i * a) := Sigma.ι_comp_desc _ _

theorem constantSchemeRightTranslation_one : constantSchemeRightTranslation S G 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro i
  exact (constantSchemeRightTranslation_label S G 1 i).trans
    ((congrArg (fun j => Sigma.ι (fun _ : G => S) j) (mul_one i)).trans (Category.comp_id _).symm)

theorem constantSchemeRightTranslation_comp (a b : G) :
    constantSchemeRightTranslation S G a ≫ constantSchemeRightTranslation S G b =
      constantSchemeRightTranslation S G (a * b) := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (constantSchemeRightTranslation S G b).left)
      (constantSchemeRightTranslation_label S G a i)).trans
        ((constantSchemeRightTranslation_label S G b (i * a)).trans
          ((congrArg (fun j => Sigma.ι (fun _ : G => S) j) (mul_assoc i a b)).trans
            (constantSchemeRightTranslation_label S G (a * b) i).symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Translations
