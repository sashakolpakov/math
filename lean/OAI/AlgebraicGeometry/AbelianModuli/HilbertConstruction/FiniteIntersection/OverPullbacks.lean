import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Functor
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Over Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! The affine overlap pullback is also a pullback in the category of schemes over the coefficient base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)
variable {S T U : Finite.AffineIntersections.finiteIntersectionIndex X} (hST : S.val ⊆ T.val) (hSU : S.val ⊆ U.val)

theorem IntersectionModel.FiniteIntersectionModel.overlap_fst_over :
    pullback.fst (M.inclusion hST) (M.inclusion hSU) ≫ M.chartMap T = M.overlapMap hST hSU := by
  change pullback.fst (M.inclusion hST) (M.inclusion hSU) ≫ M.chartMap T =
    pullback.snd (M.inclusion hST) (M.inclusion hSU) ≫ M.chartMap U
  rw [← M.inclusion_over hST, ← M.inclusion_over hSU, ← Category.assoc, ← Category.assoc,
    pullback.condition]

def IntersectionModel.FiniteIntersectionModel.overlapFstOver : M.overlapOver hST hSU ⟶ M.chartOver T :=
  Over.homMk (pullback.fst (M.inclusion hST) (M.inclusion hSU)) (M.overlap_fst_over hST hSU)

def IntersectionModel.FiniteIntersectionModel.overlapSndOver : M.overlapOver hST hSU ⟶ M.chartOver U :=
  Over.homMk (pullback.snd (M.inclusion hST) (M.inclusion hSU)) rfl

theorem IntersectionModel.FiniteIntersectionModel.overlapOver_isPullback :
    IsPullback (M.overlapFstOver hST hSU) (M.overlapSndOver hST hSU)
      (M.inclusionOver hST) (M.inclusionOver hSU) := by
  apply IsPullback.of_map (Over.forget _)
  · apply Over.OverMorphism.ext
    exact pullback.condition
  · exact IsPullback.of_hasPullback (M.inclusion hST) (M.inclusion hSU)

theorem IntersectionModel.FiniteIntersectionModel.overlapComparisonOver_fst :
    M.overlapComparisonOver hST hSU ≫ M.overlapFstOver hST hSU =
      M.inclusionOver (Unions.finiteIntersection_subset_union_left X T U) := by
  apply Over.OverMorphism.ext
  exact M.overlapComparison_fst hST hSU

theorem IntersectionModel.FiniteIntersectionModel.overlapComparisonOver_snd :
    M.overlapComparisonOver hST hSU ≫ M.overlapSndOver hST hSU =
      M.inclusionOver (Unions.finiteIntersection_subset_union_right X T U) := by
  apply Over.OverMorphism.ext
  exact M.overlapComparison_snd hST hSU

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
