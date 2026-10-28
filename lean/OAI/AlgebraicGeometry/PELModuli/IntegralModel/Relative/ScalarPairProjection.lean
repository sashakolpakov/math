import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairBaseChangeProjection

/-! # Scalar Pair Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarPairProjection

noncomputable section

/-! Scalar change and the native product projection agree through the
natural finite-product comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem relativeScalarPairProjection {S T : Scheme.{0}} (b : T ⟶ S) (X : Over S)
    (D A : Over X.left) :
    (tensorIso (ScalarIntrinsicComparison.relativeScalarNativeComparison b X D) (ScalarIntrinsicComparison.relativeScalarNativeComparison b X A)).hom.left ≫
      PairBaseChangeProjection.pairBaseChangeProjection (pullback.fst X.hom b) D A =
        (Functor.LaxMonoidal.μ (ScalarFunctor.relativeScalarFunctor b X) D A).left ≫
          pullback.fst ((Over.map X.hom).obj (D ⊗ A)).hom b := by
  have h := congrArg Over.Hom.left
    (NatTrans.IsMonoidal.tensor (τ := (ScalarIntrinsicComparison.relativeScalarNativeIso b X).hom) D A)
  have hc := congrArg (fun k => k ≫ pullback.fst (D ⊗ A).hom (pullback.fst X.hom b)) h
  change
    ((Functor.LaxMonoidal.μ (ScalarFunctor.relativeScalarFunctor b X) D A).left ≫
      (ScalarIntrinsicComparison.relativeScalarNativeComparison b X (D ⊗ A)).hom.left) ≫ _ =
    ((tensorIso (ScalarIntrinsicComparison.relativeScalarNativeComparison b X D) (ScalarIntrinsicComparison.relativeScalarNativeComparison b X A)).hom.left ≫
      (Functor.LaxMonoidal.μ (Over.pullback (pullback.fst X.hom b)) D A).left) ≫ _ at hc
  rw [Category.assoc, ScalarIntrinsicComparison.relativeScalarNativeComparison_fst, Category.assoc] at hc
  exact hc.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarPairProjection
