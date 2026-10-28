import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectionGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatesOver

/-! # Product Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductComparison

noncomputable section

/-! The globally constructed comparison from the Segre equation scheme to the projective product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) (n m : ℕ)

abbrev segreEquationScheme :=
  ProjectiveScheme.segreProjectiveScheme (σ := ULift.{u} (Fin (n + 1))) (τ := ULift.{u} (Fin (m + 1))) R

abbrev segreEquationOver :=
  ProjectiveScheme.segreProjectiveOver (σ := ULift.{u} (Fin (n + 1))) (τ := ULift.{u} (Fin (m + 1))) R

theorem segreRowProjection_over :
    ProjectionGluing.segreRowProjection R n m ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom = (segreEquationOver R n m).hom := by
  apply (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (HomogeneousRelations.segreHomogeneousIdeal R)).openCover.hom_ext
  intro p
  change ChartProjections.SegreProjectiveIndex.{u} n m at p
  change (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ _ =
    (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ _
  have h := (AffineProjective.CoordinatesOver.affineProjectiveCoordinateMap_over R (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (fun a => ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) p.1.down
    (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2)).trans (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).w.symm
  exact (Category.assoc (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
    (ProjectionGluing.segreRowProjection R n m) (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom).symm.trans
      ((congrArg (fun f => f ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom)
        (ProjectionGluing.segreRowProjection_chart R p)).trans h)

theorem segreColumnProjection_over :
    ProjectionGluing.segreColumnProjection R n m ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R m).hom = (segreEquationOver R n m).hom := by
  apply (HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective.projectiveQuotientAffineCover (HomogeneousRelations.segreHomogeneousIdeal R)).openCover.hom_ext
  intro p
  change ChartProjections.SegreProjectiveIndex.{u} n m at p
  change (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ _ =
    (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ _
  have h := (AffineProjective.CoordinatesOver.affineProjectiveCoordinateMap_over R (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (fun b => ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) p.2.down
    (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2)).trans (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).w.symm
  exact (Category.assoc (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
    (ProjectionGluing.segreColumnProjection R n m) (Projective.ProjectivePresentations.affineProjectiveSpace R m).hom).symm.trans
      ((congrArg (fun f => f ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R m).hom)
        (ProjectionGluing.segreColumnProjection_chart R p)).trans h)

def segreRowProjectionOver : segreEquationOver R n m ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n :=
  Over.homMk (ProjectionGluing.segreRowProjection R n m) (segreRowProjection_over R n m)

def segreColumnProjectionOver : segreEquationOver R n m ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R m :=
  Over.homMk (ProjectionGluing.segreColumnProjection R n m) (segreColumnProjection_over R n m)

def segreToProduct : segreEquationScheme R n m ⟶
    pullback (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom (Projective.ProjectivePresentations.affineProjectiveSpace R m).hom :=
  pullback.lift (ProjectionGluing.segreRowProjection R n m) (ProjectionGluing.segreColumnProjection R n m)
    ((segreRowProjection_over R n m).trans (segreColumnProjection_over R n m).symm)

theorem segreToProduct_fst :
    segreToProduct R n m ≫ pullback.fst _ _ = ProjectionGluing.segreRowProjection R n m := pullback.lift_fst _ _ _

theorem segreToProduct_snd :
    segreToProduct R n m ≫ pullback.snd _ _ = ProjectionGluing.segreColumnProjection R n m := pullback.lift_snd _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductComparison
