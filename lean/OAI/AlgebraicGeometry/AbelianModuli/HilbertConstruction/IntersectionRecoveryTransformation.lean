import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntersectionRecoveryNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramComparison
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered

/-! # Intersection Recovery Transformation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Recovery of the base-changed intersection diagram is an equifibered natural transformation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : FiniteIntersection.IntersectionModel.FiniteIntersectionModel X)
variable (D : Subalgebra M.coefficients R)

def FiniteIntersection.IntersectionModel.FiniteIntersectionModel.intersectionRecoveryNat :
    ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R)) ⟶ M.baseChangedSchemeFunctor D where
  app S := M.chartBaseChangeRecovery D S
  naturality _ _ h := M.chartBaseChangeRecovery_natural D h

theorem FiniteIntersection.IntersectionModel.FiniteIntersectionModel.intersectionRecoveryNat_equifibered : (M.intersectionRecoveryNat D).Equifibered := by
  intro S T h
  exact (Cartesian.DiagramComparison.isPullback_arrow_of_base_squares
    (M.chartBaseChangeRecovery D S) (M.chartBaseChangeRecovery D T)
    (Finite.AffineIntersections.finiteIntersectionChart X S).hom (Finite.AffineIntersections.finiteIntersectionChart X T).hom
    ((M.baseChangedFunctor D).obj S).hom ((M.baseChangedFunctor D).obj T).hom
    (Spec.map (CommRingCat.ofHom D.val.toRingHom))
    ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).map h).left ((M.baseChangedFunctor D).map h).left
    (M.chartBaseChangeRecovery_isPullback D S) (M.chartBaseChangeRecovery_isPullback D T)
    ((ReferenceIntersectionFunctor.originalIntersectionFunctor X).map h).w ((M.baseChangedFunctor D).map h).w
    (M.chartBaseChangeRecovery_natural D h).symm).flip

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
