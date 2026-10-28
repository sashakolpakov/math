import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairDualZeroSquare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.DualFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Line.IsoFromDescent

/-! # Pair Dual Zero Recovery -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual dual-zero restriction of the descended Poincare line
recovers its full ordinary descent datum and its adjusted cover frame. -/

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
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroLineDatum : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData
    (fun (_ : PUnit.{1}) => B.abelianCover) :=
  Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum B.productCoverOver.left B.abelianCover
    ((Over.pullback b).map U.prescribedPoincareDualZero).left B.dualZeroSection B.productCover_dualZero
    (B.poincareLineDatum hrigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroDatumFrame : (B.dualZeroLineDatum hrigid).obj PUnit.unit ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback b).obj U.prescribedTotalSpace).left :=
  U.scalarPoincareDualFrame b

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroDatumFrame_eq : B.dualZeroDatumFrame hrigid = U.scalarPoincareDualFrame b := rfl

variable [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.abelian.scheme.left :=
  (B.poincareLine hrigid).pullback B.dualZeroSection

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroLine_def : B.dualZeroLine hrigid =
    (B.poincareLine hrigid).pullback B.dualZeroSection := rfl

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroLineDatumIso :
    Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum B.abelianCover (B.dualZeroLine hrigid).sheaf ≅
      B.dualZeroLineDatum hrigid :=
  OrdinaryLineBundleRecovery.fpqcDescendedLineBundleSquareDatumIso B.productCoverOver.left (B.poincareLineDatum hrigid)
    (U.scalarPoincareLine b).locallyTrivial B.abelianCover
    ((Over.pullback b).map U.prescribedPoincareDualZero).left B.dualZeroSection B.productCover_dualZero

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroDatumRecovery : ((B.dualZeroLine hrigid).pullback B.abelianCover).sheaf ≅
    (B.dualZeroLineDatum hrigid).obj PUnit.unit :=
  Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks B.abelianCover (B.dualZeroLineDatumIso hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroDatumRecovery_compatible :
    (Scheme.Modules.pullback (pullback.fst B.abelianCover B.abelianCover)).map
        (B.dualZeroDatumRecovery hrigid).hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing B.abelianCover (B.dualZeroLineDatum hrigid)).hom =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing B.abelianCover
      (pullback.fst B.abelianCover B.abelianCover) (pullback.snd B.abelianCover B.abelianCover)
      pullback.condition).hom.app (B.dualZeroLine hrigid).sheaf ≫
        (Scheme.Modules.pullback (pullback.snd B.abelianCover B.abelianCover)).map
          (B.dualZeroDatumRecovery hrigid).hom :=
  Line.IsoFromDescent.ordinaryLineDatumIso_compatible B.abelianCover (B.dualZeroLineDatum hrigid)
    (B.dualZeroLine hrigid).sheaf (B.dualZeroLineDatumIso hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
