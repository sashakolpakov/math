import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLocalProduct
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarPairProjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComparedPairProjection

/-! # Pair Local Dual Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Both native family comparisons give the same original Poincare
projection as the inverse of the actual scalar product comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localDualData_projection :
    (B.dualNativeComparison.inv ⊗ₘ B.abelianNativeComparison.inv).left ≫
      PairBaseChangeProjection.pairBaseChangeProjection (pullback.fst X.hom b)
        U.forgetAuxiliary.data.polarized.dual.abelian.scheme U.forgetAuxiliary.data.polarized.abelian.scheme =
      B.localProductComparison.inv.left ≫ pullback.fst U.prescribedPoincareSpace.hom b :=
  ComparedPairProjection.comparedPairProjection (Relative.ScalarFunctor.relativeScalarFunctor b X) _ _
    (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X U.forgetAuxiliary.data.polarized.dual.abelian.scheme)
    (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X U.forgetAuxiliary.data.polarized.abelian.scheme)
    B.dualComparison B.abelianComparison (pullback.fst U.prescribedPoincareSpace.hom b)
    (PairBaseChangeProjection.pairBaseChangeProjection (pullback.fst X.hom b) _ _)
    (Relative.ScalarPairProjection.relativeScalarPairProjection b X _ _)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
