import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ToGrassmannian

/-! # Chart Preimages -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartPreimages.Grassmannian

noncomputable section

/-! The global Plücker map pulls back each matrix chart to its projective basic open. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (R : CommRingCat.{u}) (a b : ι → ν)

theorem grassmannianChart_preimage_chart (S : Scheme.{u}) :
    Grassmannian.Gluing.grassmannianChartMap a S ⁻¹ᵁ (Grassmannian.Gluing.grassmannianChartMap b S).opensRange =
      (Normalized.Chart.Grassmannian.normalizedChart a S).left.basicOpen (Normalized.Overlap.Grassmannian.normalizedPivotSection a b S) := by
  let h := Grassmannian.Gluing.grassmannianChart_intersection_isPullback a b S
  calc
    _ = (pullback.fst (Grassmannian.Gluing.grassmannianChartMap a S) (Grassmannian.Gluing.grassmannianChartMap b S)).opensRange :=
      (Scheme.Hom.opensRange_pullbackFst _ _).symm
    _ = (h.isoPullback.hom ≫ pullback.fst _ _).opensRange :=
      (Scheme.Hom.opensRange_comp_of_isIso _ _).symm
    _ = (Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b S).left.opensRange := by
      apply TopologicalSpace.Opens.ext
      exact congrArg (fun f : (Normalized.Overlap.Grassmannian.normalizedChartOverlap a b S).left ⟶ (Normalized.Chart.Grassmannian.normalizedChart a S).left =>
        Set.range f) h.isoPullback_hom_fst
    _ = _ := Scheme.Opens.opensRange_ι _

theorem pluckerChartSchemeIso_pivot :
    (Chart.Grassmannian.pluckerChartSchemeIso R a).hom.left.appTop (Normalized.Overlap.Grassmannian.normalizedPivotSection a b (Spec R)) =
      Chart.Grassmannian.pluckerChartSection R a b := by
  let f := (Chart.Grassmannian.pluckerChartSchemeIso R a).hom
  have hQ := Overlap.Grassmannian.pluckerChartSchemeIso_matrix R a (𝟙 (Chart.Grassmannian.pluckerChartScheme R a))
  rw [Category.id_comp] at hQ
  calc
    _ = Determinants.Grassmannian.maximalMinor (Normalized.AtlasMaps.Grassmannian.chartMatrix a (Spec R) f) b :=
      ((congrArg (fun Q => Determinants.Grassmannian.maximalMinor Q b)
        (Normalized.Chart.Grassmannian.normalizedChartRepresentation_apply a (Spec R) f)).trans
        (Determinants.Grassmannian.maximalMinor_map f.left.appTop.hom b (Normalized.Chart.Grassmannian.universalNormalizedMatrix a (Spec R)))).symm
    _ = Determinants.Grassmannian.maximalMinor (Chart.Grassmannian.pluckerChartSchemePointEquiv R a (Chart.Grassmannian.pluckerChartScheme R a) (𝟙 _)).val b :=
      congrArg (fun Q => Determinants.Grassmannian.maximalMinor Q b) hQ
    _ = _ := Chart.Grassmannian.pluckerChartSchemePointEquiv_minor R a b (𝟙 _)

theorem pluckerProjectiveChart_preimage_basicOpen :
    (Projective.Grassmannian.pluckerProjectiveChartMap R a).left ⁻¹ᵁ
        Proj.basicOpen (OverlapAlgebra.Grassmannian.pluckerQuotientGrading (R := R) (ι := ι) (ν := ν)) (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) b).val =
      (Chart.Grassmannian.pluckerChartScheme R a).left.basicOpen (Chart.Grassmannian.pluckerChartSection R a b) := by
  have h := Proj.awayι_preimage_basicOpen
    (OverlapAlgebra.Grassmannian.pluckerQuotientGrading (R := R) (ι := ι) (ν := ν))
    (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) a).property Nat.zero_lt_one
    (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) b).property Nat.zero_lt_one
  have he : HomogeneousLocalization.Away.isLocalizationElem
      (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) a).property (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) b).property =
      Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a (X b) := by
    simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one, OverlapAlgebra.Grassmannian.pluckerVariable] using
      (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_homogeneous (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a (isHomogeneous_X R b)).symm
  exact h.trans ((congrArg PrimeSpectrum.basicOpen he).trans
    (basicOpen_eq_of_affine (R := CommRingCat.of (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a))
      (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a (X b))).symm)

theorem pluckerToGrassmannian_preimage_chart :
    ToGrassmannian.Grassmannian.pluckerToGrassmannian (ι := ι) (ν := ν) R ⁻¹ᵁ (Grassmannian.Gluing.grassmannianChartMap a (Spec R)).opensRange =
      Proj.basicOpen (OverlapAlgebra.Grassmannian.pluckerQuotientGrading (R := R) (ι := ι) (ν := ν)) (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) a).val := by
  have h (b : ι → ν) :
      (Projective.Grassmannian.pluckerProjectiveChartMap R b).left ⁻¹ᵁ
          (ToGrassmannian.Grassmannian.pluckerToGrassmannian (ι := ι) (ν := ν) R ⁻¹ᵁ (Grassmannian.Gluing.grassmannianChartMap a (Spec R)).opensRange) =
        (Projective.Grassmannian.pluckerProjectiveChartMap R b).left ⁻¹ᵁ
          Proj.basicOpen (OverlapAlgebra.Grassmannian.pluckerQuotientGrading (R := R) (ι := ι) (ν := ν)) (OverlapAlgebra.Grassmannian.pluckerVariable (R := R) a).val := by
    calc
      _ = ((Projective.Grassmannian.pluckerProjectiveChartMap R b).left ≫ ToGrassmannian.Grassmannian.pluckerToGrassmannian (ι := ι) (ν := ν) R) ⁻¹ᵁ
          (Grassmannian.Gluing.grassmannianChartMap a (Spec R)).opensRange := (Scheme.Hom.comp_preimage _ _ _).symm
      _ = ((Chart.Grassmannian.pluckerChartSchemeIso R b).hom.left ≫ Grassmannian.Gluing.grassmannianChartMap b (Spec R)) ⁻¹ᵁ
          (Grassmannian.Gluing.grassmannianChartMap a (Spec R)).opensRange :=
        congrArg (fun f => f ⁻¹ᵁ (Grassmannian.Gluing.grassmannianChartMap a (Spec R)).opensRange)
          (ToGrassmannian.Grassmannian.pluckerToGrassmannian_chart R b)
      _ = _ := by
        rw [Scheme.Hom.comp_preimage, grassmannianChart_preimage_chart, Scheme.preimage_basicOpen_top,
          pluckerChartSchemeIso_pivot, pluckerProjectiveChart_preimage_basicOpen]
  ext x
  obtain ⟨b, y, rfl⟩ := Projective.Grassmannian.pluckerProjectiveCharts_cover R x
  exact (congrArg (fun U : (Chart.Grassmannian.pluckerChartScheme R b).left.Opens => y ∈ U) (h b)).to_iff

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartPreimages.Grassmannian
