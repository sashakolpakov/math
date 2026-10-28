import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.BaseChangedSectionConstants

/-! # Relative Picard Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.RelativePicardInjectivity

noncomputable section

/-! Picard class equality for a pointed proper reduced connected scheme over a field gives actual bundle isomorphisms on arbitrary test schemes, after identifying section fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K]
variable (P : Over (Spec (.of K))) [UniversallyClosed P.hom] [IsSeparated P.hom]
variable [IsReduced P.left] [ConnectedSpace P.left]
variable (x : Spec (.of K) ⟶ P.left) (hx : x ≫ P.hom = 𝟙 _)
variable (T : Over (Spec (.of K))) (L M : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor P).obj T))
variable (y : T.left ⟶ (Picard.PicardSheaf.familySchemeFunctor P).obj T)
variable (hy : y ≫ Limits.pullback.fst T.hom P.hom = 𝟙 _)
variable (b : (Scheme.Modules.pullback y).obj L.sheaf ≅ (Scheme.Modules.pullback y).obj M.sheaf)

include x hx hy b in
theorem properField_bundleIso_of_relativePicard_eq
    (h : (Picard.PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) :=
  Picard.ClassIsoDescent.bundleIso_of_relativePicard_eq P T L M y hy b
    (BaseChangedSectionConstants.properField_iteratedBaseChangeSection_bijective P.hom x hx
      (IsPullback.of_hasPullback T.hom P.hom).flip y hy) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.RelativePicardInjectivity
