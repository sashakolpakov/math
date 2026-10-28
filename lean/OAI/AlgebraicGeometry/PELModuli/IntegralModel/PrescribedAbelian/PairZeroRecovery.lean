import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZeroSquare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.ZeroFrame

/-! # Pair Zero Recovery -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The descended Poincare line restricted to the actual abelian zero
section recovers the original framed line on the dual cover. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLineDatum : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData
    (fun (_ : PUnit.{1}) => B.dualCover) :=
  Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum B.productCoverOver.left B.dualCover
    ((Over.pullback b).map U.prescribedPoincareZero).left B.abelianZeroSection B.productCover_abelianZero
    (B.poincareLineDatum hrigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLineRecovery :
    (((B.poincareLine hrigid).pullback B.abelianZeroSection).pullback B.dualCover).sheaf ≅
      ((U.scalarPoincareLine b).pullback ((Over.pullback b).map U.prescribedPoincareZero).left).sheaf :=
  OrdinaryLineBundleRecovery.fpqcDescendedLineBundleSquareRecovery B.productCoverOver.left (B.poincareLineDatum hrigid)
    (U.scalarPoincareLine b).locallyTrivial B.dualCover
    ((Over.pullback b).map U.prescribedPoincareZero).left B.abelianZeroSection B.productCover_abelianZero

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLineDatumIso :
    Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum B.dualCover
      ((B.poincareLine hrigid).pullback B.abelianZeroSection).sheaf ≅ B.abelianZeroLineDatum hrigid :=
  OrdinaryLineBundleRecovery.fpqcDescendedLineBundleSquareDatumIso B.productCoverOver.left (B.poincareLineDatum hrigid)
    (U.scalarPoincareLine b).locallyTrivial B.dualCover
    ((Over.pullback b).map U.prescribedPoincareZero).left B.abelianZeroSection B.productCover_abelianZero

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLineCoverFrame :
    (((B.poincareLine hrigid).pullback B.abelianZeroSection).pullback B.dualCover).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback b).obj U.prescribedDualTotalSpace).left :=
  B.abelianZeroLineRecovery hrigid ≪≫ U.scalarPoincareZeroFrame b

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
