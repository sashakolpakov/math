import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.OverlapOver
import Mathlib.CategoryTheory.Category.Preorder

/-! # Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! The descended inclusion maps form a functor from the reverse finite-subset order. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)

def IntersectionModel.FiniteIntersectionModel.inclusionOver {S T : Finite.AffineIntersections.finiteIntersectionIndex X} (h : S.val ⊆ T.val) :
    M.chartOver T ⟶ M.chartOver S := Over.homMk (M.inclusion h) (M.inclusion_over h)

theorem IntersectionModel.FiniteIntersectionModel.inclusionOver_id (S : Finite.AffineIntersections.finiteIntersectionIndex X) :
    M.inclusionOver (Finset.Subset.refl S.val) = 𝟙 (M.chartOver S) := by
  apply Over.OverMorphism.ext
  exact M.inclusion_id S

theorem IntersectionModel.FiniteIntersectionModel.inclusionOver_comp {S T U : Finite.AffineIntersections.finiteIntersectionIndex X}
    (hST : S.val ⊆ T.val) (hTU : T.val ⊆ U.val) :
    M.inclusionOver hTU ≫ M.inclusionOver hST = M.inclusionOver (hST.trans hTU) := by
  apply Over.OverMorphism.ext
  exact M.inclusion_comp hST hTU

def IntersectionModel.FiniteIntersectionModel.intersectionFunctor : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ ⥤ Over (Spec (.of M.coefficients)) where
  obj S := M.chartOver S
  map h := M.inclusionOver (leOfHom h)
  map_id S := M.inclusionOver_id S
  map_comp f g := (M.inclusionOver_comp (leOfHom g) (leOfHom f)).symm

instance IntersectionModel.FiniteIntersectionModel.intersectionFunctor_open {S T : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ} (h : S ⟶ T) :
    IsOpenImmersion (M.intersectionFunctor.map h).left := M.inclusion_open (leOfHom h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
