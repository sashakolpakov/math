import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointNormalization

/-! # At Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Poincare bundle classified by the identity of the dual is trivial on the whole test family. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u
variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

def Dual.Data.DualAbelianData.poincareAt_oneIso (D : Dual.Data.DualAbelianData A) (T : Over S) :
    (D.poincareAt (1 : T ⟶ D.abelian.scheme)).sheaf ≅
      Line.Bundles.structureModule ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T) := by
  have h : (Picard.PicardSheaf.familySchemeFunctor A.scheme).map (1 : T ⟶ D.abelian.scheme) =
      (snd T A.scheme).left ≫ (lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)).left := by
    have he : (1 : T ⟶ D.abelian.scheme) ▷ A.scheme =
        snd T A.scheme ≫ lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [whiskerRight_fst, Category.assoc, lift_fst, MonObj.comp_one]
      · simp only [whiskerRight_snd, Category.assoc, lift_snd, Category.comp_id]
    exact congrArg Over.Hom.left he
  exact (Scheme.Modules.pullbackCongr h).app D.poincare.sheaf ≪≫
    ((Scheme.Modules.pullbackComp (snd T A.scheme).left
      (lift (1 : A.scheme ⟶ D.abelian.scheme) (𝟙 A.scheme)).left).app D.poincare.sheaf).symm ≪≫
    (Scheme.Modules.pullback (snd T A.scheme).left).mapIso D.normalizedAtDualZero.some ≪≫
    Line.Bundles.structureModulePullbackIso (snd T A.scheme).left

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
