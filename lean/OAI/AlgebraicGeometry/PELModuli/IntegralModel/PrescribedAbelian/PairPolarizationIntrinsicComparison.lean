import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComparedFamilyMorphism

/-! # Pair Polarization Intrinsic Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The exact polarization comparison in the native abelian-scheme
base-change convention. -/

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_native_comparison :
    B.abelianNativeComparison.hom ≫
      (Over.pullback ((Over.pullback b).map π).left).map (B.polarizationMap hrigid) =
    (Over.pullback (pullback.fst X.hom b)).map U.forgetAuxiliary.data.polarized.polarization.isogeny.hom ≫
      B.dualNativeComparison.hom :=
  ComparedFamilyMorphism.compared_family_morphism
    (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X U.forgetAuxiliary.data.polarized.abelian.scheme)
    (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X U.forgetAuxiliary.data.polarized.dual.abelian.scheme)
    B.abelianComparison B.dualComparison _ _ _
    ((Relative.ScalarIntrinsicComparison.relativeScalarNativeIso b X).hom.naturality U.forgetAuxiliary.data.polarized.polarization.isogeny.hom)
    (B.polarizationMap_comparison hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
