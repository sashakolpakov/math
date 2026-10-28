import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.ModelArrows
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Unions

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! The comparison from a descended union intersection to the corresponding model pullback is open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)
variable {S T U : Finite.AffineIntersections.finiteIntersectionIndex X} (hST : S.val ⊆ T.val) (hSU : S.val ⊆ U.val)

abbrev IntersectionModel.FiniteIntersectionModel.overlapPullback : Scheme := pullback (M.inclusion hST) (M.inclusion hSU)

def IntersectionModel.FiniteIntersectionModel.overlapComparison : M.chartScheme (Unions.finiteIntersectionUnion X T U) ⟶
    M.overlapPullback hST hSU := by
  let hT := Unions.finiteIntersection_subset_union_left X T U
  let hU := Unions.finiteIntersection_subset_union_right X T U
  exact pullback.lift (M.inclusion hT) (M.inclusion hU)
    ((M.inclusion_comp hST hT).trans (M.inclusion_comp hSU hU).symm)

theorem IntersectionModel.FiniteIntersectionModel.overlapComparison_fst :
    M.overlapComparison hST hSU ≫ pullback.fst (M.inclusion hST) (M.inclusion hSU) =
      M.inclusion (S := T) (T := Unions.finiteIntersectionUnion X T U)
        (Unions.finiteIntersection_subset_union_left X T U) := pullback.lift_fst _ _ _

theorem IntersectionModel.FiniteIntersectionModel.overlapComparison_snd :
    M.overlapComparison hST hSU ≫ pullback.snd (M.inclusion hST) (M.inclusion hSU) =
      M.inclusion (S := U) (T := Unions.finiteIntersectionUnion X T U)
        (Unions.finiteIntersection_subset_union_right X T U) := pullback.lift_snd _ _ _

instance IntersectionModel.FiniteIntersectionModel.overlapComparison_open : IsOpenImmersion (M.overlapComparison hST hSU) := by
  have : IsOpenImmersion (M.inclusion hSU) := M.inclusion_open hSU
  have hp : IsOpenImmersion (pullback.fst (M.inclusion hST) (M.inclusion hSU)) := inferInstance
  have hc : IsOpenImmersion (M.overlapComparison hST hSU ≫
      pullback.fst (M.inclusion hST) (M.inclusion hSU)) := by
    rw [M.overlapComparison_fst]
    infer_instance
  exact @IsOpenImmersion.of_comp _ _ _ (M.overlapComparison hST hSU)
    (pullback.fst (M.inclusion hST) (M.inclusion hSU)) hp hc

instance IntersectionModel.FiniteIntersectionModel.overlapPullback_affine : IsAffine (M.overlapPullback hST hSU) :=
  by
    have (V : Finite.AffineIntersections.finiteIntersectionIndex X) : IsAffine (M.chartScheme V) :=
      inferInstanceAs (IsAffine (Spec (.of (M.algebra V))))
    exact inferInstanceAs (IsAffine (pullback (M.inclusion hST) (M.inclusion hSU)))

def IntersectionModel.FiniteIntersectionModel.overlapMap : M.overlapPullback hST hSU ⟶ Spec (.of M.coefficients) :=
  pullback.snd (M.inclusion hST) (M.inclusion hSU) ≫ M.chartMap U

instance IntersectionModel.FiniteIntersectionModel.overlapMap_smooth : Smooth (M.overlapMap hST hSU) :=
  inferInstanceAs (Smooth (pullback.snd (M.inclusion hST) (M.inclusion hSU) ≫ M.chartMap U))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
