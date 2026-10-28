import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Product

noncomputable section

/-! The product with a constant scheme is canonically a disjoint union of copies of the first factor, with its projection preserved. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
variable {S : Scheme.{u}} (X : Over S) (I : Type u)

def constantSchemeProductIso : (Iff.constantScheme X.left I).left ≅ (X ⊗ Iff.constantScheme S I).left :=
  (Over.forget X.left).mapIso (Constant.BaseChange.constantSchemeBaseChangeIso X.hom I) ≪≫
    pullbackSymmetry (Iff.constantScheme S I).hom X.hom

@[reassoc]
theorem constantSchemeProductIso_fst : (constantSchemeProductIso X I).hom ≫
    pullback.fst X.hom (Iff.constantScheme S I).hom = (Iff.constantScheme X.left I).hom := by
  change ((Constant.BaseChange.constantSchemeBaseChangeIso X.hom I).hom.left ≫
    (pullbackSymmetry (Iff.constantScheme S I).hom X.hom).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (Constant.BaseChange.constantSchemeBaseChangeIso X.hom I).hom.left ≫ k)
      (pullbackSymmetry_hom_comp_fst (Iff.constantScheme S I).hom X.hom)).trans
        (Constant.BaseChange.constantSchemeBaseChangeIso X.hom I).hom.w)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Product
