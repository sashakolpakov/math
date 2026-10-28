import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.LocalEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.BundleTrivializationSieve
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestFamilyPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.SheafMonoid

/-! # Base Bundle Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality

noncomputable section

/-! A bundle pulled back from the test base has trivial relative Picard class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P T : Over S) (L : Line.Bundles.LineBundle T.left)

def baseBundleFamilyPullbackIso {U : Over S} (f : U ⟶ T) :
    ((L.pullback (Limits.pullback.fst T.hom P.hom)).pullback ((PicardSheaf.familySchemeFunctor P).map f)).sheaf ≅
      ((L.pullback f.left).pullback (Limits.pullback.fst U.hom P.hom)).sheaf :=
  (Scheme.Modules.pullbackComp ((PicardSheaf.familySchemeFunctor P).map f) (Limits.pullback.fst T.hom P.hom)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (TestFamilyPullback.familySchemeFunctor_map_isPullback P f).w).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp (Limits.pullback.fst U.hom P.hom) f.left).symm.app L.sheaf

theorem baseBundle_relativePicardClass_trivial :
    (PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf (L.pullback (Limits.pullback.fst T.hom P.hom))) =
      PicardSheaf.trivialPicardClass P T := by
  apply LocalEquality.relativePicard_eq_of_local_bundle_iso P T _ _ (Base.BundleTrivializationSieve.baseBundleTrivializationSieve T L)
    (Base.BundleTrivializationSieve.baseBundleTrivializationSieve_mem_fppf T L)
  intro U f hf
  obtain ⟨e⟩ := hf
  exact ⟨baseBundleFamilyPullbackIso P T L f ≪≫
    (Scheme.Modules.pullback (Limits.pullback.fst U.hom P.hom)).mapIso e ≪≫
    Line.Bundles.structureModulePullbackIso (Limits.pullback.fst U.hom P.hom) ≪≫
    (Line.Bundles.structureModulePullbackIso ((PicardSheaf.familySchemeFunctor P).map f)).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality
