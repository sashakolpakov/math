import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RelativePicardInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Test Picard Bundle Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.TestPicardBundleIso

noncomputable section

/-! Identified section fibers and equal relative Picard classes give
actual line-bundle isomorphisms on iterated arbitrary tests of a fixed
Noetherian projective abelian family. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
variable {S T : Scheme.{u}} [IsLocallyNoetherian S] {g : ℕ}
variable (A : Abelian.Schemes.AbelianScheme g S) (PA : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (t : T ⟶ S)
variable (U : Over T) (L M : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor (A.pullback t).scheme).obj U))
variable (y : U.left ⟶ (Picard.PicardSheaf.familySchemeFunctor (A.pullback t).scheme).obj U)
variable (hy : y ≫ pullback.fst U.hom (A.pullback t).scheme.hom = 𝟙 _)
variable (b : (Scheme.Modules.pullback y).obj L.sheaf ≅ (Scheme.Modules.pullback y).obj M.sheaf)

include PA y hy b

theorem universalTest_bundleIso_of_relativePicard_eq
    (h : (Picard.PicardSheaf.toRelativePicard (A.pullback t).scheme).app (.op U) (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.toRelativePicard (A.pullback t).scheme).app (.op U) (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  have H : IsPullback
      (pullback.snd U.hom (A.pullback t).scheme.hom ≫ pullback.fst A.scheme.hom t)
      (pullback.fst U.hom (A.pullback t).scheme.hom) A.scheme.hom (U.hom ≫ t) :=
    (IsPullback.of_hasPullback U.hom (A.pullback t).scheme.hom).flip.paste_horiz
      (IsPullback.of_hasPullback A.scheme.hom t)
  exact Picard.ClassIsoDescent.bundleIso_of_relativePicard_eq (A.pullback t).scheme U L M y hy b
    (Projective.BaseChangedSectionConstants.projectivePresentation_iteratedBaseChangeSection_bijective PA η[A.scheme].left η[A.scheme].w H y hy) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.TestPicardBundleIso
