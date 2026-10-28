import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairDualZeroGluing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedLineRecovery

/-! # Dual Zero Unit Recovery -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The preserved dual-zero frame gives an actual compatible recovery
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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroUnitRecovery :
    (Scheme.Modules.pullback B.abelianCover).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.abelian.scheme.left) ≅
      (B.dualZeroLineDatum hrigid).obj PUnit.unit :=
  AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso B.abelianCover ≪≫ (B.dualZeroDatumFrame hrigid).symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroUnitRecovery_def : B.dualZeroUnitRecovery hrigid =
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso B.abelianCover ≪≫ (B.dualZeroDatumFrame hrigid).symm := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroDatumFrame_preserved_iso :
    Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso B.abelianCover (B.dualZeroLineDatum hrigid)
        (((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left ≫ B.abelianCover)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
        ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left B.abelianKernelPair.w rfl ≪≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).mapIso
        (B.dualZeroDatumFrame hrigid) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left) =
      (Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).mapIso
        (B.dualZeroDatumFrame hrigid) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left :=
  FramedLineRecovery.ordinaryOverlap_frame_iso B.abelianCover (B.dualZeroLineDatum hrigid) (B.dualZeroDatumFrame hrigid)
    (((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left ≫ B.abelianCover)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
    ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left B.abelianKernelPair.w rfl
    (B.dualZeroDatumFrame_preserved hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroUnitRecovery_compatible_iso :
    (Scheme.Modules.pullback (pullback.fst B.abelianCover B.abelianCover)).mapIso
        (B.dualZeroUnitRecovery hrigid) ≪≫
      Picard.PoincareBundle.Geometric.CechInvariant.relationGluing B.abelianCover (B.dualZeroLineDatum hrigid) =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing B.abelianCover
      (pullback.fst B.abelianCover B.abelianCover) (pullback.snd B.abelianCover B.abelianCover)
      pullback.condition).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.abelian.scheme.left) ≪≫
        (Scheme.Modules.pullback (pullback.snd B.abelianCover B.abelianCover)).mapIso
          (B.dualZeroUnitRecovery hrigid) := by
  rw [B.dualZeroUnitRecovery_def hrigid]
  exact FramedLineRecovery.framedUnitRecovery_compatible_iso B.abelianCover
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
    ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left B.abelianKernelPair
    (B.dualZeroLineDatum hrigid) (B.dualZeroDatumFrame hrigid) (B.dualZeroDatumFrame_preserved_iso hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroUnitRecovery_compatible :
    (Scheme.Modules.pullback (pullback.fst B.abelianCover B.abelianCover)).map
        (B.dualZeroUnitRecovery hrigid).hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing B.abelianCover (B.dualZeroLineDatum hrigid)).hom =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing B.abelianCover
      (pullback.fst B.abelianCover B.abelianCover) (pullback.snd B.abelianCover B.abelianCover)
      pullback.condition).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.abelian.scheme.left) ≫
        (Scheme.Modules.pullback (pullback.snd B.abelianCover B.abelianCover)).map
          (B.dualZeroUnitRecovery hrigid).hom := by
  exact FramedLineRecovery.iso_square_hom _ _ _ _ (B.dualZeroUnitRecovery_compatible_iso hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
