import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.ModelArrows
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramComparison

/-! # Cartesian Arrows -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! Every inclusion in the descended intersection diagram has a Cartesian recovery square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)

theorem IntersectionModel.FiniteIntersectionModel.inclusion_over {S T : Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    M.inclusion h ≫ M.chartMap S = M.chartMap T := M.chartArrow_over ⟨(S, T), h⟩

theorem IntersectionModel.FiniteIntersectionModel.inclusion_recovery {S T : Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    IntersectionModel.finiteIntersectionModelMap X M T ≫ M.inclusion h =
      (Arrows.finiteIntersectionArrow X h).left ≫ IntersectionModel.finiteIntersectionModelMap X M S :=
  IntersectionModel.finiteIntersectionModelMap_natural X M ⟨(S, T), h⟩

theorem IntersectionModel.FiniteIntersectionModel.inclusion_isPullback {S T : Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    IsPullback (IntersectionModel.finiteIntersectionModelMap X M T) (Arrows.finiteIntersectionArrow X h).left
      (M.inclusion h) (IntersectionModel.finiteIntersectionModelMap X M S) :=
  Cartesian.DiagramComparison.isPullback_arrow_of_base_squares _ _ _ _ _ _ _ _ _
    (IntersectionModel.finiteIntersectionModelMap_isPullback X M T)
    (IntersectionModel.finiteIntersectionModelMap_isPullback X M S)
    (Arrows.finiteIntersectionArrow X h).w (M.inclusion_over h) (M.inclusion_recovery h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
