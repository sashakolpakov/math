import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.PointsBaseChange
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-! # Scalar Functor -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarFunctor

noncomputable section

/-! Scalar change of a relative family as a finite-limit-preserving
functor. Its schemes and morphisms are the literal scalar changes of
the total-space diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

def relativeScalarFunctor {S S' : Scheme.{0}} (b : S' ⟶ S) (X : Over S) :
    Over X.left ⥤ Over ((Over.pullback b).obj X).left :=
  (Over.iteratedSliceEquiv X).inverse ⋙ Over.post (Over.pullback b) ⋙
    (Over.iteratedSliceEquiv ((Over.pullback b).obj X)).functor

instance relativeScalarFunctor_preservesFiniteLimits {S S' : Scheme.{0}} (b : S' ⟶ S) (X : Over S) :
    PreservesFiniteLimits (relativeScalarFunctor b X) := by
  dsimp [relativeScalarFunctor]
  infer_instance

instance relativeScalarFunctor_monoidal {S S' : Scheme.{0}} (b : S' ⟶ S) (X : Over S) :
    (relativeScalarFunctor b X).Monoidal := Functor.Monoidal.ofChosenFiniteProducts _

instance relativeScalarFunctor_braided {S S' : Scheme.{0}} (b : S' ⟶ S) (X : Over S) :
    (relativeScalarFunctor b X).Braided := Functor.Braided.ofChosenFiniteProducts _

theorem relativeScalarFunctor_obj {S S' : Scheme.{0}} (b : S' ⟶ S) (X : Over S) (A : Over X.left) :
    (relativeScalarFunctor b X).obj A = Over.mk
      ((Over.pullback b).map (Over.homMk A.hom : Over.mk (A.hom ≫ X.hom) ⟶ X)).left := rfl

theorem relativeScalarFunctor_map_left {S S' : Scheme.{0}} (b : S' ⟶ S) (X : Over S)
    {A B : Over X.left} (f : A ⟶ B) :
    ((relativeScalarFunctor b X).map f).left =
      ((Over.pullback b).map ((Over.map X.hom).map f)).left := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarFunctor
