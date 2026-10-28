import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.BundlePicardClass
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyFunctor

/-! # Test Family Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback

noncomputable section

/-! Maps of test schemes give Cartesian squares of the total Picard family spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} (P : Over S)

theorem familySchemeFunctor_map_isPullback {U V : Over S} (f : U ⟶ V) :
    IsPullback ((PicardSheaf.familySchemeFunctor P).map f) (Limits.pullback.fst U.hom P.hom)
      (Limits.pullback.fst V.hom P.hom) f.left := by
  have hrect : IsPullback
      ((PicardSheaf.familySchemeFunctor P).map f ≫ Limits.pullback.snd V.hom P.hom)
      (Limits.pullback.fst U.hom P.hom) P.hom (f.left ≫ V.hom) :=
    (congrArg₂ (fun a b => IsPullback a (Limits.pullback.fst U.hom P.hom) P.hom b)
      (Global.BundlePicardClass.familySchemeFunctor_map_snd P f).symm f.w.symm).mp
        (IsPullback.of_hasPullback U.hom P.hom).flip
  have hc : (PicardSheaf.familySchemeFunctor P).map f ≫ Limits.pullback.fst V.hom P.hom =
      Limits.pullback.fst U.hom P.hom ≫ f.left := Over.whiskerRight_left_fst f
  exact IsPullback.of_right hrect hc (IsPullback.of_hasPullback V.hom P.hom).flip

def picardTestBaseChangeIso {U V : Over S} (f : U ⟶ V) :
    (PicardSheaf.familySchemeFunctor P).obj U ≅ Limits.pullback f.left (Limits.pullback.fst V.hom P.hom) :=
  (familySchemeFunctor_map_isPullback P f).flip.isoPullback

theorem picardTestBaseChangeIso_inv_snd {U V : Over S} (f : U ⟶ V) :
    (picardTestBaseChangeIso P f).inv ≫ (PicardSheaf.familySchemeFunctor P).map f =
      Limits.pullback.snd f.left (Limits.pullback.fst V.hom P.hom) :=
  (familySchemeFunctor_map_isPullback P f).flip.isoPullback_inv_snd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback
