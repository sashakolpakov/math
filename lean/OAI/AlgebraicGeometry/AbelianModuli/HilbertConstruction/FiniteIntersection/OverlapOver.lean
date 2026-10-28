import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.OverlapRecovery

/-! # Overlap Over -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! The overlap comparisons are morphisms between smooth affine schemes over the coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)

abbrev IntersectionModel.FiniteIntersectionModel.chartOver (S : Finite.AffineIntersections.finiteIntersectionIndex X) : Over (Spec (.of M.coefficients)) :=
  Over.mk (M.chartMap S)

instance IntersectionModel.FiniteIntersectionModel.chartOver_affine (S : Finite.AffineIntersections.finiteIntersectionIndex X) : IsAffine (M.chartOver S).left :=
  inferInstanceAs (IsAffine (Spec (.of (M.algebra S))))

instance IntersectionModel.FiniteIntersectionModel.chartOver_smooth (S : Finite.AffineIntersections.finiteIntersectionIndex X) : Smooth (M.chartOver S).hom :=
  M.chartMap_smooth S

variable {S T U : Finite.AffineIntersections.finiteIntersectionIndex X} (hST : S.val ⊆ T.val) (hSU : S.val ⊆ U.val)

abbrev IntersectionModel.FiniteIntersectionModel.overlapOver : Over (Spec (.of M.coefficients)) := Over.mk (M.overlapMap hST hSU)

instance IntersectionModel.FiniteIntersectionModel.overlapOver_affine : IsAffine (M.overlapOver hST hSU).left :=
  M.overlapPullback_affine hST hSU

instance IntersectionModel.FiniteIntersectionModel.overlapOver_smooth : Smooth (M.overlapOver hST hSU).hom := M.overlapMap_smooth hST hSU

theorem IntersectionModel.FiniteIntersectionModel.overlapComparison_over :
    M.overlapComparison hST hSU ≫ M.overlapMap hST hSU =
      M.chartMap (Unions.finiteIntersectionUnion X T U) := by
  change M.overlapComparison hST hSU ≫
    (pullback.snd (M.inclusion hST) (M.inclusion hSU) ≫ M.chartMap U) = _
  rw [← Category.assoc, M.overlapComparison_snd]
  exact M.inclusion_over _

def IntersectionModel.FiniteIntersectionModel.overlapComparisonOver :
    M.chartOver (Unions.finiteIntersectionUnion X T U) ⟶ M.overlapOver hST hSU :=
  Over.homMk (M.overlapComparison hST hSU) (M.overlapComparison_over hST hSU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
