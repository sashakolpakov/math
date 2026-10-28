import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZeroRecovery
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.PoincareGluingIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.ZeroGluing

/-! # Pair Zero Datum Frame -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! The actual ordinary descent gluing of the abelian-zero line
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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLineDatum_gluing :
    (B.abelianZeroLineDatum hrigid).hom
        (((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left ≫ B.dualCover)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
        ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left B.dualKernelPair.w rfl =
      (U.scalarPoincareZeroGluing hU π hk hrigid b).hom := by
  let F := Over.pullback b
  let p := (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
  let q := (F.map (U.prescribedPoincareTarget π hU hk)).left
  let p' := (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
  let q' := (F.map (U.prescribedDualOverlapTarget hU π hk)).left
  let i := (F.map U.prescribedPoincareZero).left
  let r := (F.map (U.prescribedPoincareZeroOverlap π)).left
  have hs : r ≫ p = p' ≫ i := U.scalarPoincareZeroOverlap_source π b
  have ht : r ≫ q = q' ≫ i := U.scalarPoincareZeroOverlap_target hU π hk hrigid b
  have hcover : i ≫ B.productCoverOver.left = B.dualCover ≫ B.abelianZeroSection :=
    B.productCover_abelianZero
  have hb : r ≫ (q ≫ B.productCoverOver.left) = (q' ≫ B.dualCover) ≫ B.abelianZeroSection := by
    rw [← Category.assoc, ht, Category.assoc, hcover, ← Category.assoc]
  have h := Picard.PoincareBundle.Ordinary.SquareGluing.squareGluing_eq
    B.productCoverOver.left B.dualCover i B.abelianZeroSection B.productCover_abelianZero
    (B.poincareLineDatum hrigid) (q ≫ B.productCoverOver.left) p q B.productCover_kernelPair.w rfl
    (q' ≫ B.dualCover) p' q' B.dualKernelPair.w rfl r hb hs ht
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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroLineDatum_preserves_frame :
    (B.abelianZeroLineDatum hrigid).hom
        (((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left ≫ B.dualCover)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
        ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left B.dualKernelPair.w rfl ≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).mapIso
        (U.scalarPoincareZeroFrame b) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).hom =
      ((Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).mapIso
        (U.scalarPoincareZeroFrame b) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).hom := by
  rw [B.abelianZeroLineDatum_gluing hrigid]
  exact U.scalarPoincareZeroGluing_preserves_frame hU π hk hrigid b

end

/-! View the preserved zero frame as an isomorphism on the actual
source object of the ordinary descent datum. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroDatumFrame : (B.abelianZeroLineDatum hrigid).obj PUnit.unit ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback b).obj U.prescribedDualTotalSpace).left :=
  U.scalarPoincareZeroFrame b

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroDatumFrame_eq : B.abelianZeroDatumFrame hrigid = U.scalarPoincareZeroFrame b := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroDatumFrame_preserved :
    (B.abelianZeroLineDatum hrigid).hom
        (((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left ≫ B.dualCover)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
        ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left B.dualKernelPair.w rfl ≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).mapIso
        (B.abelianZeroDatumFrame hrigid) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).hom =
      ((Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).mapIso
        (B.abelianZeroDatumFrame hrigid) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).hom := by
  rw [B.abelianZeroDatumFrame_eq hrigid]
  exact B.abelianZeroLineDatum_preserves_frame hrigid

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
