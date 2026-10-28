import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.BundlePicardClass
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Family Translation Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FamilyTranslationPullback

noncomputable section

/-! Actual translated family bundles commute with a change of test scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def globalTranslatedFamilyPullbackIso (L : Line.Bundles.LineBundle A.scheme.left)
    {U T : Over S} (f : U ⟶ T) (a : T ⟶ A.scheme) :
    (((L.pullback (Limits.pullback.snd T.hom A.scheme.hom)).pullback (A.translation a).left).pullback
      ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f)).sheaf ≅
    ((L.pullback (Limits.pullback.snd U.hom A.scheme.hom)).pullback (A.translation (f ≫ a)).left).sheaf :=
  (Scheme.Modules.pullbackComp ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f) (A.translation a).left).app
      (L.pullback (Limits.pullback.snd T.hom A.scheme.hom)).sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (A.translation_naturality f a)).symm).app
      (L.pullback (Limits.pullback.snd T.hom A.scheme.hom)).sheaf ≪≫
    (Scheme.Modules.pullbackComp (A.translation (f ≫ a)).left ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map f)).symm.app
      (L.pullback (Limits.pullback.snd T.hom A.scheme.hom)).sheaf ≪≫
    (Scheme.Modules.pullback (A.translation (f ≫ a)).left).mapIso
      (BundlePicardClass.globalBundleFamilyPullbackIso A.scheme L f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FamilyTranslationPullback
