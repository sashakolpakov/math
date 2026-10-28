import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairDualZeroGluing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairDualZeroRecovery
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.DualZeroUnitRecovery
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedLineRecovery

/-! # Pair Dual Zero Trivial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended Poincare line is trivial on the dual-zero
section, by descent of the prescribed invariant frame. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

variable [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroLine_trivial :
    Nonempty ((B.dualZeroLine hrigid).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.abelian.scheme.left) :=
  Line.IsoFromDescent.lineIso_of_ordinaryRecoveries B.abelianCover (B.dualZeroLineDatum hrigid)
    (B.dualZeroLine hrigid) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial B.abelian.scheme.left)
    (B.dualZeroDatumRecovery hrigid) (B.dualZeroUnitRecovery hrigid)
    (B.dualZeroDatumRecovery_compatible hrigid) (B.dualZeroUnitRecovery_compatible hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLine_dualZero_trivial :
    Nonempty (((B.poincareLine hrigid).pullback B.dualZeroSection).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.abelian.scheme.left) := by
  rw [← B.dualZeroLine_def hrigid]
  exact B.dualZeroLine_trivial hrigid

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
