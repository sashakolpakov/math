import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationIsogeny
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyPairComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyTypeBaseDescent

/-! # Pair Polarization Type -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended polarization isogeny has the original
prescribed finite-flat degree and geometric kernel type. -/

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
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationIsogeny_local_type :
    ((B.polarizationIsogeny hrigid).pullback ((Over.pullback b).map π).left).HasPolarizationType
      P.polarizationType :=
  IsogenyPairComparison.isogenyPolarizationType_of_pairComparison
    (U.forgetAuxiliary.data.polarized.polarization.isogeny.pullback (pullback.fst X.hom b))
    ((B.polarizationIsogeny hrigid).pullback ((Over.pullback b).map π).left)
    B.abelianNativeComparison B.dualNativeComparison (B.polarizationMap_native_comparison hrigid).symm
    (U.forgetAuxiliary.data.polarized.polarization.kernelType.pullback (pullback.fst X.hom b))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationIsogeny_type :
    (B.polarizationIsogeny hrigid).HasPolarizationType P.polarizationType := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact IsogenyTypeBaseDescent.isogenyType_of_baseChange (B.polarizationIsogeny hrigid) ((Over.pullback b).map π).left
    (B.polarizationIsogeny_local_type hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
