import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZeroRecovery
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Line.IsoFromDescent

/-! # Pair Zero Datum Recovery -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Express the actual zero-line recovery with its target given by
the source object of the ordinary descent datum. -/

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
    [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.dual.scheme.left :=
  (B.poincareLine hrigid).pullback B.abelianZeroSection

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLine_def : B.abelianZeroLine hrigid =
    (B.poincareLine hrigid).pullback B.abelianZeroSection := rfl

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroDatumRecovery : ((B.abelianZeroLine hrigid).pullback B.dualCover).sheaf ≅
    (B.abelianZeroLineDatum hrigid).obj PUnit.unit :=
  Picard.PoincareBundle.DescentComponentIsomorphisms.componentIso
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks B.dualCover (B.abelianZeroLineDatumIso hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroDatumRecovery_compatible :
    (Scheme.Modules.pullback (pullback.fst B.dualCover B.dualCover)).map
        (B.abelianZeroDatumRecovery hrigid).hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing B.dualCover (B.abelianZeroLineDatum hrigid)).hom =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing B.dualCover
      (pullback.fst B.dualCover B.dualCover) (pullback.snd B.dualCover B.dualCover)
      pullback.condition).hom.app (B.abelianZeroLine hrigid).sheaf ≫
        (Scheme.Modules.pullback (pullback.snd B.dualCover B.dualCover)).map
          (B.abelianZeroDatumRecovery hrigid).hom :=
  Line.IsoFromDescent.ordinaryLineDatumIso_compatible B.dualCover (B.abelianZeroLineDatum hrigid)
    (B.abelianZeroLine hrigid).sheaf (B.abelianZeroLineDatumIso hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
