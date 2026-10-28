import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairProduct
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FunctorPairCover

/-! # Pair Local Product -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual scalar product cover agrees with the product of the
prescribed cartesian family comparisons. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localProductComparison :
    (Relative.ScalarFunctor.relativeScalarFunctor b X).obj
      (U.forgetAuxiliary.data.polarized.dual.abelian.scheme ⊗ U.forgetAuxiliary.data.polarized.abelian.scheme) ≅
        (B.dual.pullback ((Over.pullback b).map π).left).scheme ⊗
          (B.abelian.pullback ((Over.pullback b).map π).left).scheme :=
  FunctorPairComparison.functorPairComparison (Relative.ScalarFunctor.relativeScalarFunctor b X) _ _ B.dualComparison B.abelianComparison

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localProductComparison_fst :
    B.localProductComparison.hom.left ≫
      (fst (B.dual.pullback ((Over.pullback b).map π).left).scheme
        (B.abelian.pullback ((Over.pullback b).map π).left).scheme).left =
      ((Over.pullback b).map U.prescribedPoincareDual).left ≫ B.dualComparison.hom.left :=
  congrArg Over.Hom.left (FunctorPairComparison.functorPairComparison_fst (Relative.ScalarFunctor.relativeScalarFunctor b X) _ _
    B.dualComparison B.abelianComparison)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localProductComparison_snd :
    B.localProductComparison.hom.left ≫
      (snd (B.dual.pullback ((Over.pullback b).map π).left).scheme
        (B.abelian.pullback ((Over.pullback b).map π).left).scheme).left =
      ((Over.pullback b).map U.prescribedPoincareAbelian).left ≫ B.abelianComparison.hom.left :=
  congrArg Over.Hom.left (FunctorPairComparison.functorPairComparison_snd (Relative.ScalarFunctor.relativeScalarFunctor b X) _ _
    B.dualComparison B.abelianComparison)

variable [Surjective π.left]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localProductComparison_cover :
    B.localProductComparison.hom.left ≫
      PairBaseChangeProjection.pairBaseChangeProjection ((Over.pullback b).map π).left B.dual.scheme B.abelian.scheme =
        B.productCover :=
  FunctorPairCover.functorPairComparison_cover ((Over.pullback b).map π).left (Relative.ScalarFunctor.relativeScalarFunctor b X) _ _
    B.dual.scheme B.abelian.scheme B.dualComparison B.abelianComparison
    B.dualCover B.abelianCover B.productCover B.dualComparison_cover B.abelianComparison_cover
    B.productCover_dual B.productCover_abelian

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localProductComparison_inv_cover :
    B.localProductComparison.inv.left ≫ B.productCover =
      PairBaseChangeProjection.pairBaseChangeProjection ((Over.pullback b).map π).left B.dual.scheme B.abelian.scheme := by
  rw [← B.localProductComparison_cover, ← Category.assoc, ← Over.comp_left,
    B.localProductComparison.inv_hom_id, Over.id_left, Category.id_comp]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
