import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.DiagonalFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FactorizationIdeal

/-! # Morphism Equality Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityIdeal

noncomputable section

/-! Equality of two morphisms from a proper flat family to a separated family has an actual defining ideal, with its exact condition on every base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : Over S}
variable [IsProper X.hom] [Flat X.hom] [IsSeparated Y.hom] (u v : X ⟶ Y)

def properMorphismEqualityIdeal : S.IdealSheafData := FactorizationIdeal.properFactorizationIdeal (Family.DiagonalFactorization.familyDiagonal Y) (lift u v)

theorem properMorphismEqualityIdeal_test {T : Scheme.{u}} (c : T ⟶ S) :
    (properMorphismEqualityIdeal u v).comap c = ⊥ ↔ (Over.pullback c).map u = (Over.pullback c).map v :=
  (FactorizationIdeal.properFactorizationIdeal_test (Family.DiagonalFactorization.familyDiagonal Y) (lift u v) c).trans
    (Family.DiagonalFactorization.overPullback_equal_iff_diagonal_factorization c u v).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.MorphismEqualityIdeal
