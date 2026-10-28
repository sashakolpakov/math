import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.FunctionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChangeLabels

/-! # Open Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenFunctions

noncomputable section

/-! On every open subset of the base, the constant scheme is still the disjoint union of those opens and its regular functions have actual label coordinates. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (S : Scheme.{u}) (I : Type u) (U : S.Opens)

def constantSchemeOpenIso :
    (Iff.constantScheme U.toScheme I).left ≅ ((Iff.constantScheme S I).hom ⁻¹ᵁ U).toScheme :=
  (Over.forget U.toScheme).mapIso (Constant.BaseChange.constantSchemeBaseChangeIso U.ι I) ≪≫
    (isPullback_morphismRestrict (Iff.constantScheme S I).hom U).flip.isoPullback.symm

theorem constantSchemeOpenIso_inclusion :
    (constantSchemeOpenIso S I U).hom ≫ ((Iff.constantScheme S I).hom ⁻¹ᵁ U).ι =
      (Constant.BaseChange.constantSchemeBaseChangeIso U.ι I).hom.left ≫ pullback.fst (Iff.constantScheme S I).hom U.ι :=
  (Category.assoc _ _ _).trans (congrArg
    (fun k => (Constant.BaseChange.constantSchemeBaseChangeIso U.ι I).hom.left ≫ k)
      (isPullback_morphismRestrict (Iff.constantScheme S I).hom U).flip.isoPullback_inv_fst)

theorem constantSchemeOpenIso_label_inclusion (i : I) :
    Sigma.ι (fun _ : I => U.toScheme) i ≫ (constantSchemeOpenIso S I U).hom ≫
      ((Iff.constantScheme S I).hom ⁻¹ᵁ U).ι = U.ι ≫ Sigma.ι (fun _ : I => S) i :=
  (congrArg (fun k => Sigma.ι (fun _ : I => U.toScheme) i ≫ k)
    (constantSchemeOpenIso_inclusion S I U)).trans
      ((Category.assoc _ _ _).symm.trans (Constant.BaseChangeLabels.constantSchemeBaseChangeIso_label_fst U.ι I i))

def constantSchemeOpenRingIso :
    Γ((Iff.constantScheme S I).left, (Iff.constantScheme S I).hom ⁻¹ᵁ U) ≅
      CommRingCat.of (I → Γ(U.toScheme, ⊤)) :=
  ((Iff.constantScheme S I).hom ⁻¹ᵁ U).topIso.symm ≪≫
    Scheme.Γ.mapIso (constantSchemeOpenIso S I U).op ≪≫
      GlobalFunctions.constantSchemeGlobalRingIso U.toScheme I

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.OpenFunctions
