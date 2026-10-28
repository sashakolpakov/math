import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizedComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FppfConditions

/-! # Pair Rosati -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended polarized family and integral action satisfy
the prescribed Rosati conjugation, detected by faithful pullback of the
constructed dual endomorphism equations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.rosati_local [IsLocallyNoetherian ((Over.pullback b).obj Q).left] : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation
    ((B.polarizedData hrigid).pullback ((Over.pullback b).map π).left)
    ((B.integralAction hrigid).pullback ((Over.pullback b).map π).left) :=
  RosatiIsoTransport.rosati_of_polarized_iso (B.polarizedComparison hrigid)
    (U.forgetAuxiliary.data.action.pullback (pullback.fst X.hom b))
    ((B.integralAction hrigid).pullback ((Over.pullback b).map π).left)
    (fun r => (B.polarizedActionComparison hrigid).action r |>.symm)
    (PEL.BaseChange.rosati_pullback U.forgetAuxiliary.data.polarized U.forgetAuxiliary.data.action
      U.forgetAuxiliary.rosati (pullback.fst X.hom b))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.rosati [IsReduced ((Over.pullback b).obj Q).left]
    [IsNoetherian ((Over.pullback b).obj Q).left] :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (B.polarizedData hrigid) (B.integralAction hrigid) := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact FppfConditions.rosati_of_fppf_baseChange ((Over.pullback b).map π).left
    (B.polarizedData hrigid) (B.integralAction hrigid) (B.rosati_local hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
