import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.DescentGluing

/-! # Poincare Gluing Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Identify the full overlap isomorphism of the actual descended
Poincare datum with its normalized scalar isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLineDatum_overlapIso :
    Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso B.productCoverOver.left (B.poincareLineDatum hrigid)
      (((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left ≫ B.productCoverOver.left)
      ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
      ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left B.productCover_kernelPair.w rfl =
        U.scalarPoincareNormalizedIso hU π hk hrigid b := by
  apply CategoryTheory.Iso.ext
  exact (Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso_hom B.productCoverOver.left
    (B.poincareLineDatum hrigid)
    (((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left ≫ B.productCoverOver.left)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    B.productCover_kernelPair.w rfl).trans
      (U.scalarPoincareLineDescentData_gluing hU π hk hrigid b B.productCoverOver B.productCover_kernelPair)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
