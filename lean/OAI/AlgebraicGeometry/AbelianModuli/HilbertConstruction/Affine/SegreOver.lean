import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

/-! # Segre Over -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SegreOver

noncomputable section

/-! The constructed Segre closed immersion is a projective presentation over the coefficient base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable (R : CommRingCat.{u}) (n m : ℕ)

def segreProductOverIso :
    Segre.ProductComparison.segreEquationOver R n m ≅ Projective.ProjectivePresentations.affineProjectiveSpace R n ⊗ Projective.ProjectivePresentations.affineProjectiveSpace R m :=
  Over.isoMk (Segre.ProjectiveIsomorphism.segreProductSchemeIso R n m) (by
    exact (Category.assoc (Segre.ProductComparison.segreToProduct R n m)
      (pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom (Projective.ProjectivePresentations.affineProjectiveSpace R m).hom)
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom).symm.trans
        ((congrArg (fun f => f ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom) (Segre.ProductComparison.segreToProduct_fst R n m)).trans
          (Segre.ProductComparison.segreRowProjection_over R n m)))

def affineSegrePolynomialOverMap : Projective.ProjectivePresentations.affineProjectiveSpace R n ⊗ Projective.ProjectivePresentations.affineProjectiveSpace R m ⟶
    Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap
      (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R)) :=
  (segreProductOverIso R n m).inv ≫ Over.homMk (Segre.ProjectiveScheme.segreProjectiveInclusion R)
    (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientInclusion_over (Segre.HomogeneousRelations.segreHomogeneousIdeal R))

instance affineSegrePolynomialOverMap_isClosedImmersion :
    IsClosedImmersion (affineSegrePolynomialOverMap R n m).left :=
  Segre.ProjectiveIsomorphism.affineSegreEmbedding_isClosedImmersion R n m

def segreProjectiveDimension : ℕ := Fintype.card (Segre.ChartProjections.SegreProjectiveIndex.{u} n m) - 1

def affineSegreStandardEmbedding : Projective.ProjectivePresentations.affineProjectiveSpace R n ⊗ Projective.ProjectivePresentations.affineProjectiveSpace R m ⟶
    Projective.ProjectivePresentations.affineProjectiveSpace R (segreProjectiveDimension.{u} n m) :=
  affineSegrePolynomialOverMap R n m ≫
    (Projective.SpaceReindex.affineProjectiveSpaceReindexIso R (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m))).hom

instance affineSegreStandardEmbedding_isClosedImmersion :
    IsClosedImmersion (affineSegreStandardEmbedding R n m).left := by
  exact @IsClosedImmersion.comp _ _ _ _ _ (affineSegrePolynomialOverMap_isClosedImmersion R n m)
    (Grassmann.ProjectivePresentation.overIso_closedImmersion
      (Projective.SpaceReindex.affineProjectiveSpaceReindexIso R (Grassmann.ProjectivePresentation.finiteProjectiveCoordinateEquiv (Segre.ChartProjections.SegreProjectiveIndex.{u} n m))))

def affineProjectiveProductPresentation :
    Projective.ProjectivePresentations.ProjectivePresentation (Projective.ProjectivePresentations.affineProjectiveSpace R n ⊗ Projective.ProjectivePresentations.affineProjectiveSpace R m) where
  dimension := segreProjectiveDimension.{u} n m
  embedding := affineSegreStandardEmbedding R n m ≫
    (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso R (segreProjectiveDimension.{u} n m)).inv
  closedImmersion := by
    exact @IsClosedImmersion.comp _ _ _ _ _ (affineSegreStandardEmbedding_isClosedImmersion R n m)
      (Grassmann.ProjectivePresentation.overIso_closedImmersion (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso R (segreProjectiveDimension.{u} n m)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SegreOver
