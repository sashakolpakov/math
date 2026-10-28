import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLocalDualProjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLocalDual
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualTransportPoincareProjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ScalarIso

/-! # Pair Local Dual Poincare -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual locally representing Poincare line recovers the scalar
original line under the prescribed product comparison. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localDualPoincareScalarIso :
    B.localDualData.poincare.sheaf ≅
      ((U.scalarPoincareLine b).pullback B.localProductComparison.inv.left).sheaf :=
  DualTransportPoincareProjection.dualTransportPoincareProjectionIso U.forgetAuxiliary.data.polarized.dual (pullback.fst X.hom b)
    B.abelianNativeComparison B.dualNativeComparison.symm ≪≫
  (Scheme.Modules.pullbackCongr B.localDualData_projection).app U.prescribedPoincareLine.sheaf ≪≫
  (Scheme.Modules.pullbackComp B.localProductComparison.inv.left
    (pullback.fst U.prescribedPoincareSpace.hom b)).symm.app U.prescribedPoincareLine.sheaf

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
