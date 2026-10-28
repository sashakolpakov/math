import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateSectionData

/-! # Affine Coordinate Section Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineCoordinateSectionData

noncomputable section

/-! Coordinates with the coefficient spectrum kept as a bundled ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
abbrev bundledAffineProjectiveSpace (R : CommRingCat.{u}) (n : ℕ) : Over (Spec R) :=
  Projective.ProjectivePresentations.affineProjectiveSpace R n
abbrev bundledAffineCoordinatePresentation (R : CommRingCat.{u}) (n : ℕ) :
    Projective.ProjectivePresentations.ProjectivePresentation (S := Spec R) (bundledAffineProjectiveSpace R n) :=
  Projective.PresentationBaseChange.nativeAffineProjectivePresentation R n

def bundledAffineCoordinateSectionData (R : CommRingCat.{u}) (n : ℕ) :
    (bundledAffineCoordinatePresentation R n).SectionData (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n) := by
  cases R with
  | of R => exact Affine.CoordinateSectionData.affineCoordinateSectionData R n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineCoordinateSectionData
