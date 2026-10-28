import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Projective
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.OverlapAlgebra
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Gluing

/-! # Overlap -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Overlap.Grassmannian

noncomputable section

/-! Compatibility of the affine Plücker chart isomorphisms on intersections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (R : CommRingCat.{u}) (a b : ι → ν)

def pluckerIntersectionScheme : Over (Spec R) := Relative.AffinePoints.relativeAffineScheme R (OverlapAlgebra.Grassmannian.pluckerDoubleChart (R := R) a b)

def pluckerIntersectionLeft : pluckerIntersectionScheme R a b ⟶ Chart.Grassmannian.pluckerChartScheme R a :=
  (algSpec R).map (CommAlgCat.ofHom (OverlapAlgebra.Grassmannian.pluckerOverlapLeft (R := R) a b)).op

def pluckerIntersectionRight : pluckerIntersectionScheme R a b ⟶ Chart.Grassmannian.pluckerChartScheme R b :=
  (algSpec R).map (CommAlgCat.ofHom (OverlapAlgebra.Grassmannian.pluckerOverlapRight (R := R) a b)).op

theorem pluckerChartSchemeIso_matrix {T : Over (Spec R)} (f : T ⟶ Chart.Grassmannian.pluckerChartScheme R a) :
    Normalized.AtlasMaps.Grassmannian.chartMatrix a (Spec R) (f ≫ (Chart.Grassmannian.pluckerChartSchemeIso R a).hom) =
      (Chart.Grassmannian.pluckerChartSchemePointEquiv R a T f).val :=
  congrArg Subtype.val (ConcreteCategory.congr_hom
    (NatTrans.congr_app (Chart.Grassmannian.pluckerChartSchemeIso_representation R a) (.op T)) f)

theorem pluckerIntersectionLeft_matrix {T : Over (Spec R)} (f : T ⟶ pluckerIntersectionScheme R a b) :
    (Chart.Grassmannian.pluckerChartSchemePointEquiv R a T (f ≫ pluckerIntersectionLeft R a b)).val =
      (OverlapAlgebra.Grassmannian.pluckerOverlapMatrixLeft (R := R) a b).map
        (Relative.AffinePoints.relativeAffinePointEquiv R (OverlapAlgebra.Grassmannian.pluckerDoubleChart (R := R) a b) T f) := by
  change (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv a
    (Relative.AffinePoints.relativeAffinePointEquiv R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a) T
      (f ≫ (algSpec R).map (CommAlgCat.ofHom (OverlapAlgebra.Grassmannian.pluckerOverlapLeft (R := R) a b)).op))).val = _
  have h := Relative.AffinePoints.relativeAffinePointEquiv_postcomp R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a)
    (OverlapAlgebra.Grassmannian.pluckerOverlapLeft (R := R) a b) f
  exact (congrArg (fun z : ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a →ₐ[R] Relative.AffinePoints.relativeGlobalAlgebra R T =>
    (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv a z).val) h).trans
    (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv_natural
      (Relative.AffinePoints.relativeAffinePointEquiv R (OverlapAlgebra.Grassmannian.pluckerDoubleChart (R := R) a b) T f) a
      (OverlapAlgebra.Grassmannian.pluckerOverlapLeft (R := R) a b))

theorem pluckerIntersectionRight_matrix {T : Over (Spec R)} (f : T ⟶ pluckerIntersectionScheme R a b) :
    (Chart.Grassmannian.pluckerChartSchemePointEquiv R b T (f ≫ pluckerIntersectionRight R a b)).val =
      (OverlapAlgebra.Grassmannian.pluckerOverlapMatrixRight (R := R) a b).map
        (Relative.AffinePoints.relativeAffinePointEquiv R (OverlapAlgebra.Grassmannian.pluckerDoubleChart (R := R) a b) T f) := by
  change (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv b
    (Relative.AffinePoints.relativeAffinePointEquiv R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) b) T
      (f ≫ (algSpec R).map (CommAlgCat.ofHom (OverlapAlgebra.Grassmannian.pluckerOverlapRight (R := R) a b)).op))).val = _
  have h := Relative.AffinePoints.relativeAffinePointEquiv_postcomp R (ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) b)
    (OverlapAlgebra.Grassmannian.pluckerOverlapRight (R := R) a b) f
  exact (congrArg (fun z : ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) b →ₐ[R] Relative.AffinePoints.relativeGlobalAlgebra R T =>
    (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv b z).val) h).trans
    (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv_natural
      (Relative.AffinePoints.relativeAffinePointEquiv R (OverlapAlgebra.Grassmannian.pluckerDoubleChart (R := R) a b) T f) b
      (OverlapAlgebra.Grassmannian.pluckerOverlapRight (R := R) a b))

theorem pluckerIntersection_pivot_isUnit {T : Over (Spec R)} (f : T ⟶ pluckerIntersectionScheme R a b) :
    IsUnit (Determinants.Grassmannian.maximalMinor (Chart.Grassmannian.pluckerChartSchemePointEquiv R a T (f ≫ pluckerIntersectionLeft R a b)).val b) := by
  rw [pluckerIntersectionLeft_matrix]
  let φ := Relative.AffinePoints.relativeAffinePointEquiv R (OverlapAlgebra.Grassmannian.pluckerDoubleChart (R := R) a b) T f
  exact (congrArg IsUnit (Determinants.Grassmannian.maximalMinor_map φ.toRingHom b (OverlapAlgebra.Grassmannian.pluckerOverlapMatrixLeft (R := R) a b))).mpr
    ((OverlapAlgebra.Grassmannian.pluckerOverlapMatrixLeft_pivot_isUnit (R := R) a b).map φ)

theorem pluckerIntersection_matrix_transition {T : Over (Spec R)}
    (f : T ⟶ pluckerIntersectionScheme R a b) :
    (Chart.Grassmannian.pluckerChartSchemePointEquiv R b T (f ≫ pluckerIntersectionRight R a b)).val =
      Normalized.Matrices.Grassmannian.normalizeColumns b (Chart.Grassmannian.pluckerChartSchemePointEquiv R a T (f ≫ pluckerIntersectionLeft R a b)).val := by
  rw [pluckerIntersectionRight_matrix, pluckerIntersectionLeft_matrix, OverlapAlgebra.Grassmannian.pluckerOverlapMatrix_transition]
  exact (Normalized.Matrices.Grassmannian.normalizeColumns_map
    (Relative.AffinePoints.relativeAffinePointEquiv R (OverlapAlgebra.Grassmannian.pluckerDoubleChart (R := R) a b) T f).toRingHom b _
    (OverlapAlgebra.Grassmannian.pluckerOverlapMatrixLeft_pivot_isUnit (R := R) a b)).symm

theorem grassmannianOverlap_over :
    (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b (Spec R)).hom ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a (Spec R) ≫
        Grassmannian.Gluing.grassmannianChartOverMap b (Spec R) =
      Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b (Spec R) ≫ Grassmannian.Gluing.grassmannianChartOverMap a (Spec R) := by
  apply (Over.forget (Spec R)).map_injective
  exact (Grassmannian.Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) (Spec R)).glue_condition a b

theorem pluckerIntersection_toGrassmannian :
    pluckerIntersectionLeft R a b ≫ (Chart.Grassmannian.pluckerChartSchemeIso R a).hom ≫ Grassmannian.Gluing.grassmannianChartOverMap a (Spec R) =
      pluckerIntersectionRight R a b ≫ (Chart.Grassmannian.pluckerChartSchemeIso R b).hom ≫ Grassmannian.Gluing.grassmannianChartOverMap b (Spec R) := by
  let f := pluckerIntersectionLeft R a b ≫ (Chart.Grassmannian.pluckerChartSchemeIso R a).hom
  let g := pluckerIntersectionRight R a b ≫ (Chart.Grassmannian.pluckerChartSchemeIso R b).hom
  have hu : IsUnit (Normalized.Matrices.Grassmannian.selectedColumns b (Normalized.AtlasMaps.Grassmannian.chartMatrix a (Spec R) f)).det := by
    change IsUnit (Determinants.Grassmannian.maximalMinor (Normalized.AtlasMaps.Grassmannian.chartMatrix a (Spec R) f) b)
    rw [pluckerChartSchemeIso_matrix]
    simpa only [Category.id_comp] using pluckerIntersection_pivot_isUnit R a b (𝟙 _)
  let v := Normalized.AtlasMaps.Grassmannian.overlapLift a b (Spec R) f hu
  have hv : v ≫ Normalized.Overlap.Grassmannian.normalizedOverlapInclusion a b (Spec R) = f := Normalized.AtlasMaps.Grassmannian.overlapLift_inclusion a b (Spec R) f hu
  have hw : (v ≫ (Normalized.Overlap.Grassmannian.normalizedOverlapTransition a b (Spec R)).hom) ≫
      Normalized.Overlap.Grassmannian.normalizedOverlapInclusion b a (Spec R) = g := by
    apply Normalized.AtlasMaps.Grassmannian.chartMatrix_injective b (Spec R) _
    rw [← Normalized.AtlasMaps.Grassmannian.overlapMatrix_eq_chartMatrix, Normalized.AtlasMaps.Grassmannian.overlapTransition_matrix]
    change Normalized.Matrices.Grassmannian.normalizeColumns b (Normalized.AtlasMaps.Grassmannian.overlapMatrix a b (Spec R) (Normalized.AtlasMaps.Grassmannian.overlapLift a b (Spec R) f hu)) = _
    rw [Normalized.AtlasMaps.Grassmannian.overlapLift_matrix]
    dsimp only [f, g]
    rw [pluckerChartSchemeIso_matrix, pluckerChartSchemeIso_matrix]
    have h := (pluckerIntersection_matrix_transition R a b (𝟙 _)).symm
    change @Eq (Matrix ι ν Γ((pluckerIntersectionScheme R a b).left, ⊤)) _ _ at h
    simpa only [Category.id_comp] using h
  change f ≫ Grassmannian.Gluing.grassmannianChartOverMap a (Spec R) = g ≫ Grassmannian.Gluing.grassmannianChartOverMap b (Spec R)
  rw [← hv, ← hw]
  simp only [Category.assoc, grassmannianOverlap_over]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Overlap.Grassmannian
