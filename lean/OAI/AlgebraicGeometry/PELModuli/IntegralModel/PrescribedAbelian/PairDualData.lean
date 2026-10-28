import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairDualRepresentable
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZeroTrivial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairDualZeroTrivial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairPoincareClassOrigin

/-! # Pair Dual Data -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Actual dual abelian data on the arithmetic quotient: the descended
dual represents the homogeneous Picard sheaf, and the descended line is
its universal Poincare line with both zero normalizations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid) [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualRepresentable_origin (T : Over ((Over.pullback b).obj Q).left) :
    (B.dualRepresentable hrigid).homEquiv (1 : T ⟶ B.dual.scheme) =
      B.abelian.trivialHomogeneousPicardClass T :=
  (B.dualRepresentable_apply hrigid (1 : T ⟶ B.dual.scheme)).trans
    (PairPoincareClassOrigin.pairPoincareClass_origin B.abelian B.dual (B.poincareLine hrigid)
      (B.poincareLine_homogeneous hrigid) (B.poincareLine_dualZero_trivial hrigid) T)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualData : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B.abelian where
  abelian := B.dual
  representable := B.dualRepresentable hrigid
  origin := B.dualRepresentable_origin hrigid
  poincare := B.poincareLine hrigid
  poincareHomogeneous := B.poincareLine_homogeneous hrigid
  universalClass := B.dualRepresentable_universalClass hrigid
  normalizedAtAbelianZero := B.poincareLine_abelianZero_trivial hrigid
  normalizedAtDualZero := B.poincareLine_dualZero_trivial hrigid

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualData_abelian : (B.dualData hrigid).abelian = B.dual := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualData_poincare : (B.dualData hrigid).poincare = B.poincareLine hrigid := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
