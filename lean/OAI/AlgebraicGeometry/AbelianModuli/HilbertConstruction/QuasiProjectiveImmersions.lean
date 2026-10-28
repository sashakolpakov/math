import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterLoci

/-! # Quasi Projective Immersions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A quasi-compact immersion into an actually projective scheme has an actual projective compactification and quasi-projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {X Y : Over S}

def Projective.ProjectivePresentations.ProjectivePresentation.quasiProjectiveImmersion (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (j : Y ⟶ X) [IsImmersion j.left] [QuasiCompact j.left] : Projective.ProjectivePresentations.QuasiProjectivePresentation Y := by
  let Z : Over S := Over.mk (j.left.imageι ≫ X.hom)
  let k : Z ⟶ X := Over.homMk j.left.imageι
  let a : Y ⟶ Z := Over.homMk j.left.toImage (by
    change j.left.toImage ≫ (j.left.imageι ≫ X.hom) = Y.hom
    rw [← Category.assoc, j.left.toImage_imageι, j.w])
  have : IsClosedImmersion k.left := inferInstanceAs (IsClosedImmersion j.left.imageι)
  have : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion j.left.toImage)
  have : QuasiCompact a.left := inferInstanceAs (QuasiCompact j.left.toImage)
  exact (P.ofClosedImmersion k).quasiProjectiveOpen a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
