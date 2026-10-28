import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.OverPullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappedComparisonPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.BaseChange

/-! # Base Change Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! The base-changed intersection squares are pullbacks when the overlap comparisons are isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)
variable (D : Subalgebra M.coefficients R)

abbrev IntersectionModel.FiniteIntersectionModel.coefficientSchemeBaseChange : Over (Spec (.of M.coefficients)) ⥤ Scheme :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D))) ⋙ Over.forget _

theorem IntersectionModel.FiniteIntersectionModel.baseChanged_overlap_isPullback {S T U : Finite.AffineIntersections.finiteIntersectionIndex X}
    (hST : S.val ⊆ T.val) (hSU : S.val ⊆ U.val)
    [IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D)))).map
      (M.overlapComparisonOver hST hSU))] :
    IsPullback
      ((M.coefficientSchemeBaseChange D).map (M.inclusionOver (Unions.finiteIntersection_subset_union_left X T U)))
      ((M.coefficientSchemeBaseChange D).map (M.inclusionOver (Unions.finiteIntersection_subset_union_right X T U)))
      ((M.coefficientSchemeBaseChange D).map (M.inclusionOver hST))
      ((M.coefficientSchemeBaseChange D).map (M.inclusionOver hSU)) := by
  have : IsIso ((M.coefficientSchemeBaseChange D).map (M.overlapComparisonOver hST hSU)) :=
    (Over.forget _).map_isIso _
  exact MappedComparisonPullback.isPullback_of_mapped_comparison_isIso (M.coefficientSchemeBaseChange D)
    _ _ _ _ (M.overlapOver_isPullback hST hSU) (M.overlapComparisonOver hST hSU)
    _ _ (M.overlapComparisonOver_fst hST hSU) (M.overlapComparisonOver_snd hST hSU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
