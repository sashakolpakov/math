import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.TestBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BundleIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoIdentityBaseChange

/-! # Class Iso Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent

noncomputable section

/-! Equal Picard classes yield actual bundle isomorphisms when section fibers are identified and normalization is unique after every base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (P T : Over S)
variable (L M : Line.Bundles.LineBundle ((PicardSheaf.familySchemeFunctor P).obj T))
variable (y : T.left ⟶ (PicardSheaf.familySchemeFunctor P).obj T)
variable (hy : y ≫ Limits.pullback.fst T.hom P.hom = 𝟙 _)
variable (b : (Scheme.Modules.pullback y).obj L.sheaf ≅ (Scheme.Modules.pullback y).obj M.sheaf)

include b in
theorem bundleIso_of_relativePicard_eq
    (hΓ : ∀ U : Over T.left, Function.Bijective
      ((Section.BaseChangeFunctor.familyBaseChangeSection (Limits.pullback.fst T.hom P.hom) y hy).app U).left.appTop)
    (h : (PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf L) =
      (PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let R := LocalIsomorphisms.picardBundleIsoSieve P T L M
  have hR := LocalIsomorphisms.picardBundleIsoSieve_mem_of_class_eq P T L M h
  apply (IsoIdentityBaseChange.relativeBundleIso_identity_nonempty_iff (Limits.pullback.fst T.hom P.hom) L M).mp
  apply Normalized.BundleIsoDescent.relativeBundleIso_nonempty_of_cover (Limits.pullback.fst T.hom P.hom) y hy L M b
    Scheme.fppfTopology hΓ (Over.mk (𝟙 T.left)) (Module.HomLocalSheaf.sliceBaseChangeSieve T R)
    (TestBaseSieve.sliceBaseChangeSieve_mem T Scheme.fppfTopology R hR)
  intro U f hf
  exact TestBundleTransport.picardTestBaseChange_local_iso P T U L M (TestBaseSieve.sliceBaseChangeSieve_mem_testBaseArrow T R f hf)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent
