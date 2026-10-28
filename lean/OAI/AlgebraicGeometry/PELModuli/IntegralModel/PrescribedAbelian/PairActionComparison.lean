import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairActionMap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComparedFamilyMorphism
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionBaseChangeComparison

/-! # Pair Action Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Each descended coefficient endomorphism recovers the original
native scalar action through the actual abelian group comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.actionMap_comparison (r : NumberField.RingOfIntegers E) :
    B.abelianComparison.hom ≫ (Over.pullback ((Over.pullback b).map π).left).map (B.actionMap hrigid r) =
      (Relative.ScalarFunctor.relativeScalarFunctor b X).map (U.forgetAuxiliary.data.action.map r) ≫ B.abelianComparison.hom :=
  Cartesian.FamilyMorphismComparison.cartesian_family_morphism_comparison ((Over.pullback b).map π).left _ _
    B.abelian.scheme B.abelian.scheme B.abelianComparison B.abelianComparison
    B.abelianCover B.abelianCover B.abelianComparison_cover B.abelianComparison_cover
    ((Relative.ScalarFunctor.relativeScalarFunctor b X).map (U.forgetAuxiliary.data.action.map r))
    (B.actionMap hrigid r) (B.actionMap_cover hrigid r)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.actionMap_native_comparison (r : NumberField.RingOfIntegers E) :
    B.abelianNativeComparison.hom ≫
      (Over.pullback ((Over.pullback b).map π).left).map (B.actionMap hrigid r) =
    (Over.pullback (pullback.fst X.hom b)).map (U.forgetAuxiliary.data.action.map r) ≫
      B.abelianNativeComparison.hom :=
  ComparedFamilyMorphism.compared_family_morphism
    (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X U.forgetAuxiliary.data.polarized.abelian.scheme)
    (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X U.forgetAuxiliary.data.polarized.abelian.scheme)
    B.abelianComparison B.abelianComparison _ _ _
    ((Relative.ScalarIntrinsicComparison.relativeScalarNativeIso b X).hom.naturality (U.forgetAuxiliary.data.action.map r))
    (B.actionMap_comparison hrigid r)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localAction : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E)
    (B.abelian.pullback ((Over.pullback b).map π).left) :=
  ActionBaseChangeComparison.transportIntegralAction
    (A := U.forgetAuxiliary.data.polarized.abelian.pullback (pullback.fst X.hom b))
    (B := B.abelian.pullback ((Over.pullback b).map π).left) B.abelianNativeComparison
    (U.forgetAuxiliary.data.action.pullback (pullback.fst X.hom b))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.actionMap_pullback (r : NumberField.RingOfIntegers E) :
    (Over.pullback ((Over.pullback b).map π).left).map (B.actionMap hrigid r) = B.localAction.map r :=
  Cartesian.FamilyMorphismComparison.cartesian_family_morphism_image ((Over.pullback b).map π).left _ _ _ _
    B.abelianNativeComparison B.abelianNativeComparison _ _ (B.actionMap_native_comparison hrigid r)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
