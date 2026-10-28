import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairDualZeroRecovery
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.PoincareGluingIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.DualZeroGluing

/-! # Pair Dual Zero Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual ordinary descent gluing of the dual-zero line
preserves the prescribed scalar Poincare frame. -/

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroLineDatum_gluing :
    (B.dualZeroLineDatum hrigid).hom
        (((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left ≫ B.abelianCover)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
        ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left B.abelianKernelPair.w rfl =
      (U.scalarPoincareDualZeroGluing hU π hk hrigid b).hom := by
  let F := Over.pullback b
  let p := (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
  let q := (F.map (U.prescribedPoincareTarget π hU hk)).left
  let p' := (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
  let q' := (F.map (U.prescribedOverlapTarget hU π hk)).left
  let i := (F.map U.prescribedPoincareDualZero).left
  let r := (F.map (U.prescribedPoincareDualZeroOverlap π)).left
  have hs : r ≫ p = p' ≫ i := U.scalarPoincareDualZeroOverlap_source π b
  have ht : r ≫ q = q' ≫ i := U.scalarPoincareDualZeroOverlap_target hU π hk hrigid b
  have hcover : i ≫ B.productCoverOver.left = B.abelianCover ≫ B.dualZeroSection :=
    B.productCover_dualZero
  have hb : r ≫ (q ≫ B.productCoverOver.left) = (q' ≫ B.abelianCover) ≫ B.dualZeroSection := by
    rw [← Category.assoc, ht, Category.assoc, hcover, ← Category.assoc]
  have h := Picard.PoincareBundle.Ordinary.SquareGluing.squareGluing_eq
    B.productCoverOver.left B.abelianCover i B.dualZeroSection B.productCover_dualZero
    (B.poincareLineDatum hrigid) (q ≫ B.productCoverOver.left) p q B.productCover_kernelPair.w rfl
    (q' ≫ B.abelianCover) p' q' B.abelianKernelPair.w rfl r hb hs ht
  have he : Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso B.productCoverOver.left
      (B.poincareLineDatum hrigid) (q ≫ B.productCoverOver.left) p q B.productCover_kernelPair.w rfl =
        U.scalarPoincareNormalizedIso hU π hk hrigid b :=
    B.poincareLineDatum_overlapIso hrigid
  have he' := congrArg (fun e =>
    (Picard.PoincareBundle.Ordinary.SquareGluing.pullbackSquare p p' i r hs).app (U.scalarPoincareLine b).sheaf ≪≫
      (Scheme.Modules.pullback r).mapIso e ≪≫
        ((Picard.PoincareBundle.Ordinary.SquareGluing.pullbackSquare q q' i r ht).app (U.scalarPoincareLine b).sheaf).symm) he
  have hn := LineBundle.ZeroGluing.lineBundleSquareTransportIso_eq_native (U.scalarPoincareLine b) p q i r p' q'
    hs.symm ht.symm (U.scalarPoincareNormalizedIso hU π hk hrigid b)
  exact (congrArg CategoryTheory.Iso.hom (hn.trans (he'.symm.trans h))).symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroLineDatum_preserves_frame :
    (B.dualZeroLineDatum hrigid).hom
        (((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left ≫ B.abelianCover)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
        ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left B.abelianKernelPair.w rfl ≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).mapIso
        (U.scalarPoincareDualFrame b) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).hom =
      ((Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).mapIso
        (U.scalarPoincareDualFrame b) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).hom := by
  rw [B.dualZeroLineDatum_gluing hrigid]
  exact U.scalarPoincareDualZeroGluing_preserves_frame hU π hk hrigid b

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroDatumFrame_preserved :
    (B.dualZeroLineDatum hrigid).hom
        (((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left ≫ B.abelianCover)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
        ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left B.abelianKernelPair.w rfl ≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).mapIso
        (B.dualZeroDatumFrame hrigid) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).hom =
      ((Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).mapIso
        (B.dualZeroDatumFrame hrigid) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).hom := by
  rw [B.dualZeroDatumFrame_eq hrigid]
  exact B.dualZeroLineDatum_preserves_frame hrigid

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
