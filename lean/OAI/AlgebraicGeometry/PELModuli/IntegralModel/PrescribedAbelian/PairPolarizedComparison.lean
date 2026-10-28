import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLevel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairAction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairIntrinsicPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.InverseLinePullback

/-! # Pair Polarized Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! The actual descended abelian scheme, dual, polarization, full level,
and integral action on their common arithmetic base. -/

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
    [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizedData : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N
    ((Over.pullback b).obj Q).left where
  abelian := B.abelian
  dual := B.dualData hrigid
  polarization := B.polarization hrigid
  level := B.fullLevel hrigid

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizedActionData : PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N
    ((Over.pullback b).obj Q).left where
  polarized := B.polarizedData hrigid
  action := B.integralAction hrigid

end

/-! The complete descended polarized family with action recovers the
original prescribed family through the actual native group comparisons. -/

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
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)
    [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizedComparison : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
    (U.forgetAuxiliary.data.polarized.pullback (pullback.fst X.hom b))
    ((B.polarizedData hrigid).pullback ((Over.pullback b).map π).left) where
  abelian := B.abelianNativeComparison
  dual := B.dualNativeComparison
  abelianGroup := B.abelianNativeComparison_group
  dualGroup := B.dualNativeComparison_group
  polarization := (B.polarizationMap_native_comparison hrigid).symm
  poincare := by
    let e := (Over.forget ((Over.pullback b).obj X).left).mapIso
      (B.dualNativeComparison ⊗ᵢ B.abelianNativeComparison)
    let L := (U.forgetAuxiliary.data.polarized.dual.pullback (pullback.fst X.hom b)).poincare
    let M := ((B.dualData hrigid).pullback ((Over.pullback b).map π).left).poincare
    have h : L.sheaf ≅ (M.pullback e.hom).sheaf :=
      InverseLinePullback.inverseLinePullbackIso e.symm M L (B.localPoincareNativeIso hrigid)
    exact Quotient.sound ⟨h.symm⟩
  level T c := by
    change ((U.forgetAuxiliary.data.polarized.level.pullback (pullback.fst X.hom b)).hom.app
      (.op T) c).val ≫ B.abelianNativeComparison.hom =
      (((B.fullLevel hrigid).pullback ((Over.pullback b).map π).left).hom.app (.op T) c).val
    rw [B.fullLevel_pullback hrigid]
    rfl

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizedActionComparison : PEL.Iso.PolarizedActionIso
    (U.forgetAuxiliary.data.pullback (pullback.fst X.hom b))
    ((B.polarizedActionData hrigid).pullback ((Over.pullback b).map π).left) where
  polarized := B.polarizedComparison hrigid
  action r := (B.actionMap_native_comparison hrigid r).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
