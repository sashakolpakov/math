import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Translation Section Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Fiber comparisons for translation and tensoring by a line bundle from the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (T : Over S)

def Abelian.Schemes.AbelianScheme.familyPointSection (a : T ⟶ A.scheme) : T.left ⟶ (Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T :=
  (lift (𝟙 T) a).left

theorem Abelian.Schemes.AbelianScheme.familyZeroSection_translation (a : T ⟶ A.scheme) :
    A.familyZeroSection T ≫ (A.translation a).left = A.familyPointSection T a := by
  have h : lift (𝟙 T) (1 : T ⟶ A.scheme) ≫ A.translation a = lift (𝟙 T) a := by
    simp [Abelian.Schemes.AbelianScheme.translation, MonObj.comp_mul]
  exact congrArg Over.Hom.left h

def TranslationSectionFibers.translatedBundle_zeroIso (a : T ⟶ A.scheme) (L : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T)) :
    ((L.pullback (A.translation a).left).pullback (A.familyZeroSection T)).sheaf ≅
      (L.pullback (A.familyPointSection T a)).sheaf :=
  (Scheme.Modules.pullbackComp (A.familyZeroSection T) (A.translation a).left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (A.familyZeroSection_translation T a)).app L.sheaf

def TranslationSectionFibers.baseBundle_zeroIso (B : Line.Bundles.LineBundle T.left) :
    ((B.pullback (Limits.pullback.fst T.hom A.scheme.hom)).pullback (A.familyZeroSection T)).sheaf ≅ B.sheaf :=
  (Scheme.Modules.pullbackComp (A.familyZeroSection T) (Limits.pullback.fst T.hom A.scheme.hom)).app B.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (A.familyZeroSection_fst T)).app B.sheaf ≪≫
    (Scheme.Modules.pullbackId T.left).app B.sheaf

def TranslationSectionFibers.normalizedBaseTwist_zeroIso (L : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.scheme).obj T)) (B : Line.Bundles.LineBundle T.left)
    (e₀ : (L.pullback (A.familyZeroSection T)).sheaf ≅ Line.Bundles.structureModule T.left) :
    ((L.tensor (B.pullback (Limits.pullback.fst T.hom A.scheme.hom))).pullback
      (A.familyZeroSection T)).sheaf ≅ B.sheaf :=
  Line.Bundles.LineBundle.tensorBaseChangeIso (A.familyZeroSection T) L (B.pullback (Limits.pullback.fst T.hom A.scheme.hom)) ≪≫
    Tensor.ProductSheaf.tensorModuleCongr e₀ (TranslationSectionFibers.baseBundle_zeroIso A T B) ≪≫ Tensor.ProductSheaf.tensorModuleUnitLeftIso B.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
