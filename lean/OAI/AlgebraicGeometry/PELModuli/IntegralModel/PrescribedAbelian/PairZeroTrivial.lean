import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZeroDatumFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZeroDatumRecovery
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZeroUnitRecovery
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedLineRecovery

/-! # Pair Zero Trivial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended Poincare line is trivial on the abelian-zero
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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLine_trivial :
    Nonempty ((B.abelianZeroLine hrigid).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.dual.scheme.left) :=
  Line.IsoFromDescent.lineIso_of_ordinaryRecoveries B.dualCover (B.abelianZeroLineDatum hrigid)
    (B.abelianZeroLine hrigid) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial B.dual.scheme.left)
    (B.abelianZeroDatumRecovery hrigid) (B.abelianZeroUnitRecovery hrigid)
    (B.abelianZeroDatumRecovery_compatible hrigid) (B.abelianZeroUnitRecovery_compatible hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLine_abelianZero_trivial :
    Nonempty (((B.poincareLine hrigid).pullback B.abelianZeroSection).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.dual.scheme.left) := by
  rw [← B.abelianZeroLine_def hrigid]
  exact B.abelianZeroLine_trivial hrigid

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
