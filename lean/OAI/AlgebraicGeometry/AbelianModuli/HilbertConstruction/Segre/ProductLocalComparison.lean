import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductChartScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectionPreimages

/-! # Product Local Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductLocalComparison

noncomputable section

/-! The global Segre comparison restricts to the explicitly constructed affine chart isomorphisms. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) {n m : ℕ} (p : ChartProjections.SegreProjectiveIndex.{u} n m)

theorem segreProductChartSchemeIso_row :
    ((ProductChartScheme.segreProductChartSchemeIso R p).hom ≫ Projective.ProductChartCover.projectiveProductChartMap R p) ≫
      pullback.fst _ _ = ChartProjections.segreRowChartMap R p := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (ProductChartScheme.segreProductChartSchemeIso R p).hom ≫ k)
      (Projective.ProductChartCover.projectiveProductChartMap_fst R p)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ StandardProjectiveChartOver.projectiveStandardChartInclusion R n p.1.down)
          (ProductChartScheme.segreProductChartSchemeIso_fst R p))))

theorem segreProductChartSchemeIso_column :
    ((ProductChartScheme.segreProductChartSchemeIso R p).hom ≫ Projective.ProductChartCover.projectiveProductChartMap R p) ≫
      pullback.snd _ _ = ChartProjections.segreColumnChartMap R p := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (ProductChartScheme.segreProductChartSchemeIso R p).hom ≫ k)
      (Projective.ProductChartCover.projectiveProductChartMap_snd R p)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ StandardProjectiveChartOver.projectiveStandardChartInclusion R m p.2.down)
          (ProductChartScheme.segreProductChartSchemeIso_snd R p))))

theorem segreToProduct_chart :
    (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ ProductComparison.segreToProduct R n m =
      (ProductChartScheme.segreProductChartSchemeIso R p).hom ≫ Projective.ProductChartCover.projectiveProductChartMap R p := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ k)
        (ProductComparison.segreToProduct_fst R n m)).trans
        ((ProjectionGluing.segreRowProjection_chart R p).trans (segreProductChartSchemeIso_row R p).symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ k)
        (ProductComparison.segreToProduct_snd R n m)).trans
        ((ProjectionGluing.segreColumnProjection_chart R p).trans (segreProductChartSchemeIso_column R p).symm))

theorem segreToProduct_preimage_chart :
    ProductComparison.segreToProduct R n m ⁻¹ᵁ (Projective.ProductChartCover.projectiveProductChartMap R p).opensRange =
      (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left.opensRange := by
  have he := congrArg (fun U => ProductComparison.segreToProduct R n m ⁻¹ᵁ U) (Projective.ProductChartCover.projectiveProductChartMap_opensRange R p)
  have hr := congrArg (fun f => f ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down))
    (ProductComparison.segreToProduct_fst R n m)
  have hc := congrArg (fun f => f ⁻¹ᵁ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down))
    (ProductComparison.segreToProduct_snd R n m)
  exact he.trans ((congrArg₂ (fun U V => U ⊓ V) hr hc).trans
    ((ProjectionPreimages.segreProjections_preimage R p).trans
      (Proj.opensRange_awayι (ChartCoordinates.segreQuotientGrading R) (ChartCoordinates.segreVariable R p).val
        (ChartCoordinates.segreVariable R p).property Nat.zero_lt_one).symm))

theorem segreToProduct_chart_isPullback :
    IsPullback (ProductChartScheme.segreProductChartSchemeIso R p).hom (ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
      (Projective.ProductChartCover.projectiveProductChartMap R p) (ProductComparison.segreToProduct R n m) := by
  apply IsOpenImmersion.isPullback
  · exact segreToProduct_chart R p
  · exact segreToProduct_preimage_chart R p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductLocalComparison
