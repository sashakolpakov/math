import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestBaseSieve

/-! # Test Bundle Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestBundleTransport

noncomputable section

/-! Transport local Picard bundle isomorphisms to the canonical base changes of a fixed test family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P T : Over S) (U : Over T.left)

def picardTestBaseChangeBundleIso (L : Line.Bundles.LineBundle ((PicardSheaf.familySchemeFunctor P).obj T)) :
    ((L.pullback ((PicardSheaf.familySchemeFunctor P).map (TestBaseSieve.testBaseArrow T U))).pullback
        (TestFamilyPullback.picardTestBaseChangeIso P (TestBaseSieve.testBaseArrow T U)).inv).sheaf ≅
      (L.pullback (Limits.pullback.snd U.hom (Limits.pullback.fst T.hom P.hom))).sheaf :=
  (Scheme.Modules.pullbackComp (TestFamilyPullback.picardTestBaseChangeIso P (TestBaseSieve.testBaseArrow T U)).inv
      ((PicardSheaf.familySchemeFunctor P).map (TestBaseSieve.testBaseArrow T U))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (TestFamilyPullback.picardTestBaseChangeIso_inv_snd P (TestBaseSieve.testBaseArrow T U))).app L.sheaf

theorem picardTestBaseChange_local_iso (L M : Line.Bundles.LineBundle ((PicardSheaf.familySchemeFunctor P).obj T))
    (h : LocalIsomorphisms.picardBundleIsoSieve P T L M (TestBaseSieve.testBaseArrow T U)) :
    Nonempty ((Relative.BundleIsoSheaf.relativeBundleIsoPresheaf (Limits.pullback.fst T.hom P.hom) L M).obj (.op U)) := by
  obtain ⟨e⟩ := (LocalIsomorphisms.picardBundleIsoSieve_apply P T L M (TestBaseSieve.testBaseArrow T U)).mp h
  exact ⟨(picardTestBaseChangeBundleIso P T U L).symm ≪≫
    (Scheme.Modules.pullback (TestFamilyPullback.picardTestBaseChangeIso P (TestBaseSieve.testBaseArrow T U)).inv).mapIso e ≪≫
    picardTestBaseChangeBundleIso P T U M⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestBundleTransport
