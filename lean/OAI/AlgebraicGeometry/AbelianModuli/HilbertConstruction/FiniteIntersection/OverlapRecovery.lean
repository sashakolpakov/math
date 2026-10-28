import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Comparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.CartesianArrows
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Pullbacks

/-! # Overlap Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! The model pullback recovers the original intersection, compatibly with the comparison map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)
variable {S T U : Finite.AffineIntersections.finiteIntersectionIndex X} (hST : S.val ⊆ T.val) (hSU : S.val ⊆ U.val)

def IntersectionModel.FiniteIntersectionModel.overlapRecovery : (Finite.AffineIntersections.finiteIntersectionChart X (Unions.finiteIntersectionUnion X T U)).left ⟶
    M.overlapPullback hST hSU :=
  IntersectionModel.finiteIntersectionModelMap X M (Unions.finiteIntersectionUnion X T U) ≫ M.overlapComparison hST hSU

theorem IntersectionModel.FiniteIntersectionModel.overlapRecovery_fst :
    M.overlapRecovery hST hSU ≫ pullback.fst (M.inclusion hST) (M.inclusion hSU) =
      (Arrows.finiteIntersectionArrow X (Unions.finiteIntersection_subset_union_left X T U)).left ≫
        IntersectionModel.finiteIntersectionModelMap X M T := by
  change (IntersectionModel.finiteIntersectionModelMap X M _ ≫ M.overlapComparison hST hSU) ≫ _ = _
  rw [Category.assoc, M.overlapComparison_fst]
  exact M.inclusion_recovery _

theorem IntersectionModel.FiniteIntersectionModel.overlapRecovery_snd :
    M.overlapRecovery hST hSU ≫ pullback.snd (M.inclusion hST) (M.inclusion hSU) =
      (Arrows.finiteIntersectionArrow X (Unions.finiteIntersection_subset_union_right X T U)).left ≫
        IntersectionModel.finiteIntersectionModelMap X M U := by
  change (IntersectionModel.finiteIntersectionModelMap X M _ ≫ M.overlapComparison hST hSU) ≫ _ = _
  rw [Category.assoc, M.overlapComparison_snd]
  exact M.inclusion_recovery _

theorem IntersectionModel.FiniteIntersectionModel.overlapRecovery_isPullback :
    IsPullback (M.overlapRecovery hST hSU)
      (Finite.AffineIntersections.finiteIntersectionChart X (Unions.finiteIntersectionUnion X T U)).hom
      (M.overlapMap hST hSU) (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)) := by
  let hT := Unions.finiteIntersection_subset_union_left X T U
  let hU := Unions.finiteIntersection_subset_union_right X T U
  have h := Cartesian.DiagramComparison.isPullback_comparison_recovery
    (Arrows.finiteIntersectionArrow X hT).left (Arrows.finiteIntersectionArrow X hU).left
    (Arrows.finiteIntersectionArrow X hST).left (Arrows.finiteIntersectionArrow X hSU).left
    (IntersectionModel.finiteIntersectionModelMap X M T) (IntersectionModel.finiteIntersectionModelMap X M U)
    (IntersectionModel.finiteIntersectionModelMap X M S) (M.inclusion hST) (M.inclusion hSU)
    (Finite.AffineIntersections.finiteIntersectionChart X U).hom (M.chartMap U)
    (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom))
    (Pullbacks.finiteIntersection_isPullback X hST hSU) (M.inclusion_isPullback hST)
    (IntersectionModel.finiteIntersectionModelMap_isPullback X M U) (M.inclusion_recovery hSU).symm
    (M.overlapRecovery hST hSU) (M.overlapRecovery_fst hST hSU) (M.overlapRecovery_snd hST hSU)
  exact (congrArg (fun b => IsPullback (M.overlapRecovery hST hSU) b
      (M.overlapMap hST hSU) (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)))
    (Arrows.finiteIntersectionArrow X hU).w).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
