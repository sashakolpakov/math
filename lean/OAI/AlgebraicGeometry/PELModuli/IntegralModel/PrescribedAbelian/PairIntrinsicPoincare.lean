import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairDualData
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualPoincareIntrinsicIsos

/-! # Pair Intrinsic Poincare -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual quotient Poincare line, restricted through the base cover,
is the native product pullback of the original universal Poincare line. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid) [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localPoincareNativeIso :
    ((B.dualData hrigid).pullback ((Over.pullback b).map π).left).poincare.sheaf ≅
      (((U.forgetAuxiliary.data.polarized.dual.pullback (pullback.fst X.hom b)).poincare).pullback
        (B.dualNativeComparison.inv ⊗ₘ B.abelianNativeComparison.inv).left).sheaf :=
  DualPoincareIntrinsicIsos.dualPullbackPoincarePairIso (B.dualData hrigid) ((Over.pullback b).map π).left ≪≫
    B.localPoincareIso hrigid ≪≫
      DualPoincareIntrinsicIsos.dualTransportPoincareProductIso (U.forgetAuxiliary.data.polarized.dual.pullback (pullback.fst X.hom b))
        B.abelianNativeComparison B.dualNativeComparison.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
