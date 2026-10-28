import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedMatrixPoints

/-! # Point Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointBaseChange

noncomputable section

/-! Matrix-valued Grassmannian points commute with changes of the base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable (a : ι → ν) {S T X : Scheme.{u}}

omit [Fintype ι] in
theorem chartHomOfMatrix_baseMap (f : T ⟶ S) (g : X ⟶ T)
    (Q : Matrix ι ν Γ(X, ⊤)) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    Normalized.ChartBaseChange.Grassmannian.chartHomOfMatrix a T g Q hQ ≫ Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap a f =
      Normalized.ChartBaseChange.Grassmannian.chartHomOfMatrix a S (g ≫ f) Q hQ := by
  apply Normalized.ChartBaseChange.Grassmannian.chartHom_ext a S
  · rw [Category.assoc, Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap_over, ← Category.assoc,
      Normalized.ChartBaseChange.Grassmannian.chartHomOfMatrix_over, Normalized.ChartBaseChange.Grassmannian.chartHomOfMatrix_over]
  · rw [Normalized.ChartBaseChange.Grassmannian.chartHomMatrix_comp, Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap_matrix, Normalized.ChartBaseChange.Grassmannian.chartHomOfMatrix_matrix]
    exact Normalized.ChartBaseChange.Grassmannian.chartHomOfMatrix_matrix a T g Q hQ

def matrixClassifyingSchemeMap (g : X ⟶ S) (Q : Matrix ι ν Γ(X, ⊤)) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    X ⟶ Gluing.grassmannianScheme (ι := ι) (ν := ν) S :=
  Normalized.ChartBaseChange.Grassmannian.chartHomOfMatrix a S g Q hQ ≫ Gluing.grassmannianChartMap a S

theorem matrixClassifyingSchemeMap_baseMap (f : T ⟶ S) (g : X ⟶ T)
    (Q : Matrix ι ν Γ(X, ⊤)) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    matrixClassifyingSchemeMap a g Q hQ ≫ BaseMap.grassmannianBaseMap f =
      matrixClassifyingSchemeMap a (g ≫ f) Q hQ := by
  change (Normalized.ChartBaseChange.Grassmannian.chartHomOfMatrix a T g Q hQ ≫ Gluing.grassmannianChartMap a T) ≫ BaseMap.grassmannianBaseMap f = _
  rw [Category.assoc, BaseMap.grassmannianBaseMap_chart, ← Category.assoc, chartHomOfMatrix_baseMap]
  rfl

theorem affineNormalizedClassifyingMap_left (R : CommRingCat.{u}) (A : Type u)
    [CommRing A] [Algebra R A] (Q : Matrix ι ν A) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    (Affine.NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ).left =
      matrixClassifyingSchemeMap a (Relative.AffinePoints.relativeAffineScheme R A).hom
        (Q.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
        (hQ.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.PointBaseChange
