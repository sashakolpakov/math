import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.MatrixClassifyingEquations

/-! # Chart Matrix Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartMatrixRecovery.Grassmannian

noncomputable section

/-! Recovering the coefficient-ring matrix of an affine point in a normalized chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra R A]
variable (a : ι → ν)

omit [Fintype ν] [DecidableEq ν] in
theorem affine_chart_matrix_recovery (f : Relative.AffinePoints.relativeAffineScheme R A ⟶ Normalized.Chart.Grassmannian.normalizedChart a (Spec R)) :
    ∃ (Q : Matrix ι ν A) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q),
      f ≫ Grassmannian.Gluing.grassmannianChartOverMap a (Spec R) = NormalizedMatrixPoints.Grassmannian.affineNormalizedClassifyingMap R A a Q hQ := by
  let e := Relative.AffinePoints.relativeAffineGlobalEquiv R A
  let Q := (Normalized.AtlasMaps.Grassmannian.chartMatrix a (Spec R) f).map e.symm.toRingHom
  have hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q := (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a (Spec R) f).map e.symm.toRingHom
  refine ⟨Q, hQ, ?_⟩
  change f ≫ Grassmannian.Gluing.grassmannianChartOverMap a (Spec R) =
    ((Normalized.Chart.Grassmannian.normalizedChartRepresentation a (Spec R)).app (.op (Relative.AffinePoints.relativeAffineScheme R A))).inv
      ⟨Q.map e.toRingHom, hQ.map e.toRingHom⟩ ≫ Grassmannian.Gluing.grassmannianChartOverMap a (Spec R)
  apply congrArg (fun g => g ≫ Grassmannian.Gluing.grassmannianChartOverMap a (Spec R))
  apply ((Normalized.Chart.Grassmannian.normalizedChartRepresentation a (Spec R)).app (.op (Relative.AffinePoints.relativeAffineScheme R A))).toEquiv.injective
  apply Subtype.ext
  have h := congrArg Subtype.val
    (((Normalized.Chart.Grassmannian.normalizedChartRepresentation a (Spec R)).app (.op (Relative.AffinePoints.relativeAffineScheme R A))).toEquiv.apply_symm_apply
      ⟨Q.map e.toRingHom, hQ.map e.toRingHom⟩)
  refine Eq.trans ?_ h.symm
  change Normalized.AtlasMaps.Grassmannian.chartMatrix a (Spec R) f = Q.map e.toRingHom
  ext i j
  exact (e.apply_symm_apply _).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartMatrixRecovery.Grassmannian
