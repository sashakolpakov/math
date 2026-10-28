import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianFiberComparison

/-! # Poincare Fixed Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedComparison

noncomputable section

/-! The Poincare line viewed on the descended abelian family recovers
the original line class through an explicit mixed-product isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S T : Scheme.{0}} {g : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g T}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : T ⟶ S)
    (e : A.scheme ≅ (B.pullback u).scheme)

def fixedFamilyPoincareComparison : (D.abelian.scheme ⊗ A.scheme).left ≅
    (((Over.map u).obj D.abelian.scheme) ⊗ B.scheme).left :=
  (Over.forget T).mapIso (tensorIso (Iso.refl D.abelian.scheme) e) ≪≫
    HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B.scheme u D.abelian.scheme

theorem fixedFamilyPoincareComparison_fst :
    (fixedFamilyPoincareComparison D B u e).hom ≫
      (fst ((Over.map u).obj D.abelian.scheme) B.scheme).left =
        (fst D.abelian.scheme A.scheme).left := by
  let m : (D.abelian.scheme ⊗ A.scheme).left ⟶ (D.abelian.scheme ⊗ (B.pullback u).scheme).left :=
    (𝟙 D.abelian.scheme ⊗ₘ e.hom).left
  let p : (D.abelian.scheme ⊗ (B.pullback u).scheme).left ⟶
      (((Over.map u).obj D.abelian.scheme) ⊗ B.scheme).left :=
    (HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B.scheme u D.abelian.scheme).hom
  have hp : p ≫ (fst ((Over.map u).obj D.abelian.scheme) B.scheme).left =
      (fst D.abelian.scheme (B.pullback u).scheme).left := HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_fst _ _ _
  have hm : m ≫ (fst D.abelian.scheme (B.pullback u).scheme).left =
      (fst D.abelian.scheme A.scheme).left :=
    (Over.tensorHom_left_fst _ _ (𝟙 D.abelian.scheme) e.hom).trans (Category.comp_id _)
  exact (Category.assoc m p (fst ((Over.map u).obj D.abelian.scheme) B.scheme).left).trans
    ((congrArg (fun q => m ≫ q) hp).trans hm)

theorem fixedFamilyPoincareComparison_snd :
    (fixedFamilyPoincareComparison D B u e).hom ≫
      (snd ((Over.map u).obj D.abelian.scheme) B.scheme).left =
        (snd D.abelian.scheme A.scheme).left ≫ CartesianFiberComparison.CartesianFamily.totalMap u A.scheme B.scheme e := by
  let m : (D.abelian.scheme ⊗ A.scheme).left ⟶ (D.abelian.scheme ⊗ (B.pullback u).scheme).left :=
    (𝟙 D.abelian.scheme ⊗ₘ e.hom).left
  let p : (D.abelian.scheme ⊗ (B.pullback u).scheme).left ⟶
      (((Over.map u).obj D.abelian.scheme) ⊗ B.scheme).left :=
    (HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B.scheme u D.abelian.scheme).hom
  have hp : p ≫ (snd ((Over.map u).obj D.abelian.scheme) B.scheme).left =
      (snd D.abelian.scheme (B.pullback u).scheme).left ≫ pullback.fst B.scheme.hom u :=
    HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd _ _ _
  have hm : m ≫ (snd D.abelian.scheme (B.pullback u).scheme).left =
      (snd D.abelian.scheme A.scheme).left ≫ e.hom.left :=
    Over.tensorHom_left_snd _ _ (𝟙 D.abelian.scheme) e.hom
  exact (Category.assoc m p (snd ((Over.map u).obj D.abelian.scheme) B.scheme).left).trans
    ((congrArg (fun q => m ≫ q) hp).trans
      ((Category.assoc m (snd D.abelian.scheme (B.pullback u).scheme).left (pullback.fst B.scheme.hom u)).symm.trans
        ((congrArg (fun q => q ≫ pullback.fst B.scheme.hom u) hm).trans
          (Category.assoc (snd D.abelian.scheme A.scheme).left e.hom.left (pullback.fst B.scheme.hom u)))))

theorem fixedFamilyPoincare_class : HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareFixed.fixedFamilyPoincare D B u e) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fixedFamilyPoincareComparison D B u e).inv (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) :=
  (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B.scheme u D.abelian.scheme).inv
    (𝟙 D.abelian.scheme ⊗ₘ e.inv).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm

theorem fixedFamilyPoincare_recovery_class :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fixedFamilyPoincareComparison D B u e).hom
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (PoincareFixed.fixedFamilyPoincare D B u e)) = HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare := by
  let c := fixedFamilyPoincareComparison D B u e
  exact (congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass c.hom) (fixedFamilyPoincare_class D B u e)).trans
    ((HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp c.hom c.inv (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)).symm.trans
      ((congrArg (fun q => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass q (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) c.hom_inv_id).trans
        (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare))))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareFixedComparison
