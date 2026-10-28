import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.ClassIsoDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangedSectionConstants

/-! # Relative Picard Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RelativePicardInjectivity

noncomputable section

/-! Equal relative Picard classes of normalized bundles give actual isomorphisms on arbitrary tests of a pointed proper smooth geometrically connected projective family over a locally noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable (P : Over S) [IsProper P.hom] [Smooth P.hom] [GeometricallyConnected P.hom]
variable (Q : ProjectivePresentations.ProjectivePresentation P) (x : S ⟶ P.left) (hx : x ≫ P.hom = 𝟙 _)
variable (T : Over S) (L M : Line.Bundles.LineBundle ((Picard.PicardSheaf.familySchemeFunctor P).obj T))
variable (y : T.left ⟶ (Picard.PicardSheaf.familySchemeFunctor P).obj T)
variable (hy : y ≫ Limits.pullback.fst T.hom P.hom = 𝟙 _)
variable (b : (Scheme.Modules.pullback y).obj L.sheaf ≅ (Scheme.Modules.pullback y).obj M.sheaf)

include Q x hx hy b in
theorem projective_bundleIso_of_relativePicard_eq
    (h : (Picard.PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf L) =
      (Picard.PicardSheaf.toRelativePicard P).app (.op T) (Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) :=
  Picard.ClassIsoDescent.bundleIso_of_relativePicard_eq P T L M y hy b
    (BaseChangedSectionConstants.projectivePresentation_iteratedBaseChangeSection_bijective Q x hx
      (IsPullback.of_hasPullback T.hom P.hom).flip y hy) h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RelativePicardInjectivity
