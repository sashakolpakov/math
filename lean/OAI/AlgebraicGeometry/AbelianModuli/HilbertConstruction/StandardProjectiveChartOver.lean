import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Algebra
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Standard Projective Chart Over -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveChartOver

noncomputable section

/-! Standard projective affine chart inclusions as morphisms over the coefficient spectrum. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

universe u

variable (R : CommRingCat.{u}) (n : ℕ) (i : Fin (n + 1))

def projectiveStandardChartOver : Over (Spec R) := HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme R (ProjectiveChart.Evaluation.projectiveChartRing R n i)

def projectiveStandardChartInclusion :
    (projectiveStandardChartOver R n i).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left :=
  Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (X i) (isHomogeneous_X R i) Nat.zero_lt_one

instance projectiveStandardChartInclusion_isOpenImmersion :
    IsOpenImmersion (projectiveStandardChartInclusion R n i) := by
  exact IsOpenImmersion.comp
    (Proj.basicOpenIsoSpec (Projective.ProjectivePresentations.coordinateGrading R n) (X i) (isHomogeneous_X R i) Nat.zero_lt_one).inv
    (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (X i)).ι

theorem projectiveStandardChartInclusion_over :
    projectiveStandardChartInclusion R n i ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom =
      (projectiveStandardChartOver R n i).hom := by
  have he : (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom =
      HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Projective.ProjectivePresentations.coordinateGrading R n) := by
    change Proj.toSpecZero (Projective.ProjectivePresentations.coordinateGrading R n) ≫
      Spec.map (CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom) = _
    rw [Projective.SpaceReindex.degreeZeroConstants_eq_algebraMap]
    rfl
  exact (congrArg (fun f => projectiveStandardChartInclusion R n i ≫ f) he).trans
    (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap_away (Projective.ProjectivePresentations.coordinateGrading R n) (isHomogeneous_X R i))

def projectiveStandardChartOverMap : projectiveStandardChartOver R n i ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n :=
  Over.homMk (projectiveStandardChartInclusion R n i) (projectiveStandardChartInclusion_over R n i)

theorem projectiveStandardChartInclusion_opensRange :
    (projectiveStandardChartInclusion R n i).opensRange =
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (X i) :=
  Proj.opensRange_awayι _ _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveChartOver
