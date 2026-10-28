import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairActionComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFromPullbackMaps

/-! # Pair Action -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual arithmetic quotient carries the entire original integral
action; its coefficient maps, group laws, and ring identities are descended. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.integralAction : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact Integral.ActionFromPullbackMaps.integralActionOfPullbackMaps ((Over.pullback b).map π).left B.abelian B.localAction
    (B.actionMap hrigid) (B.actionMap_pullback hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.integralAction_map (r : NumberField.RingOfIntegers E) :
    (B.integralAction hrigid).map r = B.actionMap hrigid r := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.integralAction_pullback :
    (B.integralAction hrigid).pullback ((Over.pullback b).map π).left = B.localAction := by
  apply Finite.Actions.integralAction_ext
  intro r
  exact B.actionMap_pullback hrigid r

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
