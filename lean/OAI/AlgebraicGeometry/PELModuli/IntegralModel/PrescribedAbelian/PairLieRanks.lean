import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairAction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FppfConditions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.Line

/-! # Pair Lie Ranks -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The original arithmetic Lie ranks hold on the actual quotient.
Every geometric point lifts to the scalar-changed cover, where the
native comparison identifies the original action and its Lie eigenspaces. -/

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.lieRanks_local : PEL.Has.HasIntegralLieRanks P R iotaO
    ((Over.map b).obj ((Over.pullback b).obj X))
    (B.abelian.pullback ((Over.pullback b).map π).left)
    ((B.integralAction hrigid).pullback ((Over.pullback b).map π).left) := by
  have h := PEL.BaseChange.integralLieRanks_pullback U.forgetAuxiliary.data.polarized.abelian
    U.forgetAuxiliary.data.action U.forgetAuxiliary.lieRanks ((Scalar.Line.scalarTotalProjection b).app X)
  have : IsMonHom B.abelianNativeComparison.hom := B.abelianNativeComparison_group
  exact (Integral.LieRankRestriction.integralLieRanks_iff_of_iso P iotaO ((Over.map b).obj ((Over.pullback b).obj X))
    (A := U.forgetAuxiliary.data.polarized.abelian.pullback (pullback.fst X.hom b))
    (B := B.abelian.pullback ((Over.pullback b).map π).left)
    (U.forgetAuxiliary.data.action.pullback (pullback.fst X.hom b))
    ((B.integralAction hrigid).pullback ((Over.pullback b).map π).left)
    B.abelianNativeComparison (fun r => (B.actionMap_native_comparison hrigid r).symm)).mp h

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.lieRanks : PEL.Has.HasIntegralLieRanks P R iotaO
    ((Over.map b).obj ((Over.pullback b).obj Q)) B.abelian (B.integralAction hrigid) := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  have : Surjective ((Over.map b).map ((Over.pullback b).map π)).left :=
    inferInstanceAs (Surjective ((Over.pullback b).map π).left)
  have : LocallyOfFiniteType ((Over.map b).map ((Over.pullback b).map π)).left :=
    inferInstanceAs (LocallyOfFiniteType ((Over.pullback b).map π).left)
  exact FppfConditions.integralLieRanks_of_surjective_baseChange P iotaO
    ((Over.map b).map ((Over.pullback b).map π)) B.abelian (B.integralAction hrigid) (B.lieRanks_local hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
