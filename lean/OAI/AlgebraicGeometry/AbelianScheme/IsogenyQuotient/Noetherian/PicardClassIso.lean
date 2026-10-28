import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.BundleIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent

/-! # Picard Class Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PicardClassIso.Construction

noncomputable section

/-! Equal relative Picard classes with identified section fibers
give actual bundle isomorphisms over a Noetherian parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent

variable {S : Scheme.{0}} (P T : Over S) [IsLocallyNoetherian T.left]
  [IsProper P.hom] [Smooth P.hom] [GeometricallyConnected P.hom]
  (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor P).obj T))
  (y : T.left ⟶ (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor P).obj T)
  (hy : y ≫ Limits.pullback.fst T.hom P.hom = 𝟙 _)
  (b : (Scheme.Modules.pullback y).obj L.sheaf ≅ (Scheme.Modules.pullback y).obj M.sheaf)

include b hy in
theorem noetherian_bundleIso_of_relativePicard_eq
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard P).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard P).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let R := AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms.picardBundleIsoSieve P T L M
  have hR := AbelianModuli.HilbertConstruction.Picard.LocalIsomorphisms.picardBundleIsoSieve_mem_of_class_eq P T L M h
  have : IsLocallyNoetherian (Over.mk (𝟙 T.left)).left := inferInstanceAs (IsLocallyNoetherian T.left)
  apply (AbelianModuli.HilbertConstruction.IsoIdentityBaseChange.relativeBundleIso_identity_nonempty_iff (Limits.pullback.fst T.hom P.hom) L M).mp
  apply BundleIsoDescent.Construction.noetherian_relativeBundleIso_nonempty_of_cover (Limits.pullback.fst T.hom P.hom) y hy L M b
    (Over.mk (𝟙 T.left)) (AbelianModuli.HilbertConstruction.Module.HomLocalSheaf.sliceBaseChangeSieve T R)
    (AbelianModuli.HilbertConstruction.Picard.TestBaseSieve.sliceBaseChangeSieve_mem T Scheme.fppfTopology R hR)
  intro U _ f hf
  exact AbelianModuli.HilbertConstruction.Picard.TestBundleTransport.picardTestBaseChange_local_iso P T U L M (AbelianModuli.HilbertConstruction.Picard.TestBaseSieve.sliceBaseChangeSieve_mem_testBaseArrow T R f hf)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.PicardClassIso.Construction
