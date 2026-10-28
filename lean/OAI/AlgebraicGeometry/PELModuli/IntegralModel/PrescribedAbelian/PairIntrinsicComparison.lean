import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.Pair
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarIntrinsicComparison

/-! # Pair Intrinsic Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The two actual cartesian group comparisons expressed in the native
abelian-scheme pullback convention. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianNativeComparison :
    (U.forgetAuxiliary.data.polarized.abelian.pullback (pullback.fst X.hom b)).scheme ≅
      (B.abelian.pullback ((Over.pullback b).map π).left).scheme :=
  (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X U.forgetAuxiliary.data.polarized.abelian.scheme).symm ≪≫
    B.abelianComparison

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianNativeComparison_group : IsMonHom B.abelianNativeComparison.hom := by
  have := Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison_isMonHom b X U.forgetAuxiliary.data.polarized.abelian.scheme
  have := B.abelianComparison_group
  change IsMonHom ((Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X
    U.forgetAuxiliary.data.polarized.abelian.scheme).inv ≫ B.abelianComparison.hom)
  infer_instance

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualNativeComparison :
    (U.forgetAuxiliary.data.polarized.dual.abelian.pullback (pullback.fst X.hom b)).scheme ≅
      (B.dual.pullback ((Over.pullback b).map π).left).scheme :=
  (Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X U.forgetAuxiliary.data.polarized.dual.abelian.scheme).symm ≪≫
    B.dualComparison

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualNativeComparison_group : IsMonHom B.dualNativeComparison.hom := by
  have := Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison_isMonHom b X U.forgetAuxiliary.data.polarized.dual.abelian.scheme
  have := B.dualComparison_group
  change IsMonHom ((Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X
    U.forgetAuxiliary.data.polarized.dual.abelian.scheme).inv ≫ B.dualComparison.hom)
  infer_instance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
