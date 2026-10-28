import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DualRepresentingTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport

/-! # Pair Local Dual -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Over the prescribed base cover, the actual descended dual represents
the homogeneous Picard sheaf of the actual descended abelian scheme.
This is constructed from the original universal dual and both cartesian
group comparisons. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localDualData : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData (B.abelian.pullback ((Over.pullback b).map π).left) :=
  DualRepresentingTransport.dualRepresentingTransport
    ((U.forgetAuxiliary.data.polarized.dual.pullback (pullback.fst X.hom b)).familyTransport
      B.abelianNativeComparison) B.dualNativeComparison.symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localDualData_abelian :
    B.localDualData.abelian = B.dual.pullback ((Over.pullback b).map π).left := rfl

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localDualRepresentable :
    (B.abelian.pullback ((Over.pullback b).map π).left).homogeneousPicardSheaf.obj.RepresentableBy
      (B.dual.pullback ((Over.pullback b).map π).left).scheme :=
  B.localDualData.representable

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localDualRepresentable_origin (T : Over ((Over.pullback b).obj X).left) :
    B.localDualRepresentable.homEquiv (1 : T ⟶ (B.dual.pullback ((Over.pullback b).map π).left).scheme) =
      (B.abelian.pullback ((Over.pullback b).map π).left).trivialHomogeneousPicardClass T :=
  B.localDualData.origin T

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
