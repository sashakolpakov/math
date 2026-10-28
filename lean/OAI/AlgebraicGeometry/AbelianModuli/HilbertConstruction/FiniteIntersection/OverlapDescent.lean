import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.OverlapOver
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.SpanIndex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AffineComparisonDescent

/-! # Overlap Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! All overlap comparison coordinate maps become isomorphisms over one finite coefficient extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)

abbrev IntersectionModel.FiniteIntersectionModel.spanChart (j : SpanIndex.finiteIntersectionSpanIndex X) : Over (Spec (.of M.coefficients)) :=
  M.chartOver (SpanIndex.finiteIntersectionSpanUnion X j)

abbrev IntersectionModel.FiniteIntersectionModel.spanOverlap (j : SpanIndex.finiteIntersectionSpanIndex X) : Over (Spec (.of M.coefficients)) :=
  M.overlapOver (SpanIndex.finiteIntersectionSpan_left X j) (SpanIndex.finiteIntersectionSpan_right X j)

def IntersectionModel.FiniteIntersectionModel.spanComparison (j : SpanIndex.finiteIntersectionSpanIndex X) : M.spanChart j ⟶ M.spanOverlap j :=
  M.overlapComparisonOver (SpanIndex.finiteIntersectionSpan_left X j) (SpanIndex.finiteIntersectionSpan_right X j)

def IntersectionModel.FiniteIntersectionModel.spanComparisonAlgebra (j : SpanIndex.finiteIntersectionSpanIndex X) :
    Affine.OverChartPoints.affineOverAlgebra M.coefficients (M.spanOverlap j) →ₐ[M.coefficients]
      Affine.OverChartPoints.affineOverAlgebra M.coefficients (M.spanChart j) := Affine.OverMorphisms.affineOverMap M.coefficients (M.spanComparison j)

theorem IntersectionModel.FiniteIntersectionModel.exists_common_overlap_tensor_bijective
    (E : Subalgebra M.coefficients R) (hE : E.FG) :
    ∃ D : Subalgebra M.coefficients R, E ≤ D ∧ D.FG ∧
      ∀ j, Function.Bijective
        (Algebra.TensorProduct.map (AlgHom.id D D) (M.spanComparisonAlgebra j)) := by
  exact Finite.AffineComparisonDescent.exists_common_affine_comparison_tensor_bijective (M.spanChart) (M.spanOverlap)
    M.spanComparison (fun j => Finite.AffineIntersections.finiteIntersectionChart X (SpanIndex.finiteIntersectionSpanUnion X j))
    (fun j => IntersectionModel.finiteIntersectionModelMap X M (SpanIndex.finiteIntersectionSpanUnion X j))
    (fun j => M.overlapRecovery (SpanIndex.finiteIntersectionSpan_left X j) (SpanIndex.finiteIntersectionSpan_right X j))
    (fun j => IntersectionModel.finiteIntersectionModelMap_isPullback X M (SpanIndex.finiteIntersectionSpanUnion X j))
    (fun j => M.overlapRecovery_isPullback (SpanIndex.finiteIntersectionSpan_left X j)
      (SpanIndex.finiteIntersectionSpan_right X j))
    (fun _ => rfl) E hE

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
