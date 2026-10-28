import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatePreimages

/-! # Projection Preimages -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectionPreimages

noncomputable section

/-! The paired row and column chart opens pull back to exactly the Segre coordinate chart. -/

open _root_.MvPolynomial _root_.HomogeneousLocalization _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) {n m : ℕ}

theorem segreHomogeneousChart_preimage_basicOpen
    (p q : ChartProjections.SegreProjectiveIndex.{u} n m) :
    (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ⁻¹ᵁ
      Proj.basicOpen (ChartCoordinates.segreQuotientGrading R) (ChartCoordinates.segreVariable R q).val =
        PrimeSpectrum.basicOpen (ChartCoordinates.segreChartCoordinate R p.1 p.2 q) := by
  have h := Proj.awayι_preimage_basicOpen (ChartCoordinates.segreQuotientGrading R)
    (ChartCoordinates.segreVariable R p).property Nat.zero_lt_one (ChartCoordinates.segreVariable R q).property Nat.zero_lt_one
  have he : HomogeneousLocalization.Away.isLocalizationElem
      (ChartCoordinates.segreVariable R p).property (ChartCoordinates.segreVariable R q).property =
        ChartCoordinates.segreChartCoordinate R p.1 p.2 q := by
    have hc := (HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_homogeneous (HomogeneousRelations.segreHomogeneousIdeal R) p (isHomogeneous_X R q)).symm
    simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one, ChartCoordinates.segreVariable]
    exact hc
  exact h.trans (congrArg PrimeSpectrum.basicOpen he)

theorem segreChartProjections_preimage (p q : ChartProjections.SegreProjectiveIndex.{u} n m) :
    (ChartProjections.segreRowChartMap R p ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (X q.1.down)) ⊓
      (ChartProjections.segreColumnChartMap R p ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R m) (X q.2.down)) =
        (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ⁻¹ᵁ
          Proj.basicOpen (ChartCoordinates.segreQuotientGrading R) (ChartCoordinates.segreVariable R q).val := by
  have hr := AffineProjective.CoordinatePreimages.affineProjectiveCoordinateMap_preimage R (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (fun a => ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) p.1.down
      (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2) q.1.down
  have hc := AffineProjective.CoordinatePreimages.affineProjectiveCoordinateMap_preimage R (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (fun b => ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) p.2.down
      (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2) q.2.down
  have he := congrArg₂ (fun U V => U ⊓ V) hr hc
  exact he.trans ((PrimeSpectrum.basicOpen_mul
    (ChartCoordinates.segreChartCoordinate R p.1 p.2 (q.1, p.2))
    (ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, q.2))).symm.trans
      ((congrArg PrimeSpectrum.basicOpen (ChartCoordinates.segreChartCoordinate_entry R p.1 q.1 p.2 q.2).symm).trans
        (segreHomogeneousChart_preimage_basicOpen R p q).symm))

theorem segreProjections_preimage (q : ChartProjections.SegreProjectiveIndex.{u} n m) :
    (ProjectionGluing.segreRowProjection R n m ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (X q.1.down)) ⊓
      (ProjectionGluing.segreColumnProjection R n m ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R m) (X q.2.down)) =
        Proj.basicOpen (ChartCoordinates.segreQuotientGrading R) (ChartCoordinates.segreVariable R q).val := by
  ext x
  obtain ⟨i, j, y, rfl⟩ := ProjectiveScheme.segreHomogeneousCharts_cover R x
  let p : ChartProjections.SegreProjectiveIndex.{u} n m := (i, j)
  have hr := congrArg (fun f => f ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (X q.1.down))
    (ProjectionGluing.segreRowProjection_chart R p)
  have hc := congrArg (fun f => f ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R m) (X q.2.down))
    (ProjectionGluing.segreColumnProjection_chart R p)
  have he := (congrArg₂ (fun U V => U ⊓ V) hr hc).trans (segreChartProjections_preimage R p q)
  exact (congrArg (fun U => y ∈ U) he).to_iff

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectionPreimages
