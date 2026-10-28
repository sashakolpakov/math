import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Morphisms

noncomputable section

/-! A morphism from a constant scheme is exactly one section for each label. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable (S : Scheme.{u}) (I : Type u)

def constantSchemeLabelPoint (i : I) : 𝟙_ (Over S) ⟶ Iff.constantScheme S I :=
  Over.homMk (Sigma.ι (fun _ : I => S) i) (Iff.constantScheme_ι_hom i)

def constantSchemeMorphismEquiv (Y : Over S) :
    (Iff.constantScheme S I ⟶ Y) ≃ (I → (𝟙_ (Over S) ⟶ Y)) where
  toFun f i := constantSchemeLabelPoint S I i ≫ f
  invFun p := Over.homMk (Sigma.desc (fun i => (p i).left)) (by
    apply Sigma.hom_ext
    intro i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a : S ⟶ Y.left => a ≫ Y.hom) (Sigma.ι_comp_desc (fun i => (p i).left) i)).trans
        ((p i).w.trans (Iff.constantScheme_ι_hom i).symm)))
  left_inv f := by
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    exact Sigma.ι_comp_desc _ _
  right_inv p := by
    funext i
    apply Over.OverMorphism.ext
    exact Sigma.ι_comp_desc _ _

theorem constantSchemeMorphismEquiv_postcomp {Y Z : Over S}
    (f : Iff.constantScheme S I ⟶ Y) (g : Y ⟶ Z) (i : I) :
    constantSchemeMorphismEquiv S I Z (f ≫ g) i = constantSchemeMorphismEquiv S I Y f i ≫ g :=
  (Category.assoc (constantSchemeLabelPoint S I i) f g).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Morphisms
