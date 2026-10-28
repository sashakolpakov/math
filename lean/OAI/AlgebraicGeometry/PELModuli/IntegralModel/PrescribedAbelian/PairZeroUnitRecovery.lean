import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZeroDatumFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedLineRecovery

/-! # Pair Zero Unit Recovery -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The preserved zero frame gives an actual compatible recovery
of the trivial quotient line, before comparing quotient line bundles. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroUnitRecovery :
    (Scheme.Modules.pullback B.dualCover).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.dual.scheme.left) ≅
      (B.abelianZeroLineDatum hrigid).obj PUnit.unit :=
  AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso B.dualCover ≪≫ (B.abelianZeroDatumFrame hrigid).symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroUnitRecovery_def : B.abelianZeroUnitRecovery hrigid =
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso B.dualCover ≪≫ (B.abelianZeroDatumFrame hrigid).symm := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroDatumFrame_preserved_iso :
    Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso B.dualCover (B.abelianZeroLineDatum hrigid)
        (((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left ≫ B.dualCover)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
        ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left B.dualKernelPair.w rfl ≪≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).mapIso
        (B.abelianZeroDatumFrame hrigid) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left) =
      (Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).mapIso
        (B.abelianZeroDatumFrame hrigid) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left :=
  FramedLineRecovery.ordinaryOverlap_frame_iso B.dualCover (B.abelianZeroLineDatum hrigid) (B.abelianZeroDatumFrame hrigid)
    (((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left ≫ B.dualCover)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
    ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left B.dualKernelPair.w rfl
    (B.abelianZeroDatumFrame_preserved hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroUnitRecovery_compatible_iso :
    (Scheme.Modules.pullback (pullback.fst B.dualCover B.dualCover)).mapIso
        (B.abelianZeroUnitRecovery hrigid) ≪≫
      Picard.PoincareBundle.Geometric.CechInvariant.relationGluing B.dualCover (B.abelianZeroLineDatum hrigid) =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing B.dualCover
      (pullback.fst B.dualCover B.dualCover) (pullback.snd B.dualCover B.dualCover)
      pullback.condition).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.dual.scheme.left) ≪≫
        (Scheme.Modules.pullback (pullback.snd B.dualCover B.dualCover)).mapIso
          (B.abelianZeroUnitRecovery hrigid) := by
  rw [B.abelianZeroUnitRecovery_def hrigid]
  exact FramedLineRecovery.framedUnitRecovery_compatible_iso B.dualCover
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
    ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left B.dualKernelPair
    (B.abelianZeroLineDatum hrigid) (B.abelianZeroDatumFrame hrigid) (B.abelianZeroDatumFrame_preserved_iso hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroUnitRecovery_compatible :
    (Scheme.Modules.pullback (pullback.fst B.dualCover B.dualCover)).map
        (B.abelianZeroUnitRecovery hrigid).hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing B.dualCover (B.abelianZeroLineDatum hrigid)).hom =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing B.dualCover
      (pullback.fst B.dualCover B.dualCover) (pullback.snd B.dualCover B.dualCover)
      pullback.condition).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.dual.scheme.left) ≫
        (Scheme.Modules.pullback (pullback.snd B.dualCover B.dualCover)).map
          (B.abelianZeroUnitRecovery hrigid).hom := by
  exact FramedLineRecovery.iso_square_hom _ _ _ _ (B.abelianZeroUnitRecovery_compatible_iso hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
