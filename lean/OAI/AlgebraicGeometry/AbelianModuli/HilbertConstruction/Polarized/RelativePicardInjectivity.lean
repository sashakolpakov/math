import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.IteratedSectionConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent

/-! # Relative Picard Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Equal relative Picard classes of bundles with identified section fibers give actual bundle isomorphisms on every test of a polarized locally Noetherian family. No projective presentation is supplied. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.bundleIso_of_relativePicard_eq
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (T : Over S)
    (L M : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor A.abelian.scheme).obj T))
    (y : T.left ⟶ (Picard.PicardSheaf.familySchemeFunctor A.abelian.scheme).obj T)
    (hy : y ≫ Limits.pullback.fst T.hom A.abelian.scheme.hom = 𝟙 _)
    (b : (Scheme.Modules.pullback y).obj L.sheaf ≅ (Scheme.Modules.pullback y).obj M.sheaf)
    (h : (Picard.PicardSheaf.toRelativePicard A.abelian.scheme).app (.op T) (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.toRelativePicard A.abelian.scheme).app (.op T) (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) :=
  Picard.ClassIsoDescent.bundleIso_of_relativePicard_eq A.abelian.scheme T L M y hy b
    (A.iteratedBaseChangeSection_globalFunctions_bijective
      (IsPullback.of_hasPullback T.hom A.abelian.scheme.hom).flip y hy) h

theorem PolarizationData.PolarizedAbelianWithFullLevel.baseChanged_bundleIso_of_relativePicard_eq
    {S T : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S) (U : Over T)
    (L M : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor (A.pullback f).abelian.scheme).obj U))
    (y : U.left ⟶ (Picard.PicardSheaf.familySchemeFunctor (A.pullback f).abelian.scheme).obj U)
    (hy : y ≫ Limits.pullback.fst U.hom (A.pullback f).abelian.scheme.hom = 𝟙 _)
    (b : (Scheme.Modules.pullback y).obj L.sheaf ≅ (Scheme.Modules.pullback y).obj M.sheaf)
    (h : (Picard.PicardSheaf.toRelativePicard (A.pullback f).abelian.scheme).app (.op U) (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.toRelativePicard (A.pullback f).abelian.scheme).app (.op U) (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  have H : IsPullback
      (Limits.pullback.snd U.hom (A.pullback f).abelian.scheme.hom ≫ Limits.pullback.fst A.abelian.scheme.hom f)
      (Limits.pullback.fst U.hom (A.pullback f).abelian.scheme.hom) A.abelian.scheme.hom (U.hom ≫ f) :=
    (IsPullback.of_hasPullback U.hom (A.pullback f).abelian.scheme.hom).flip.paste_horiz
      (IsPullback.of_hasPullback A.abelian.scheme.hom f)
  exact Picard.ClassIsoDescent.bundleIso_of_relativePicard_eq (A.pullback f).abelian.scheme U L M y hy b
    (A.iteratedBaseChangeSection_globalFunctions_bijective H y hy) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
