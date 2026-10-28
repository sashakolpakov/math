import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.Dual
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.ZeroGluingHom

/-! # Dual Zero Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The scalar Poincare isomorphism induces a framed gluing
isomorphism on its actual dual-zero line. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualZeroGluing :
    (((U.scalarPoincareLine b).pullback ((Over.pullback b).map U.prescribedPoincareDualZero).left).pullback
      ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).sheaf ≅
    (((U.scalarPoincareLine b).pullback ((Over.pullback b).map U.prescribedPoincareDualZero).left).pullback
      ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).sheaf :=
  LineBundle.SquareIsoFrames.lineBundleSquareTransportIso (U.scalarPoincareLine b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    ((Over.pullback b).map U.prescribedPoincareDualZero).left
    ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
    ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left
    (U.scalarPoincareDualZeroOverlap_source π b).symm
    (U.scalarPoincareDualZeroOverlap_target hU π hk hrigid b).symm
    (U.scalarPoincareNormalizedIso hU π hk hrigid b)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualZeroGluing_def : U.scalarPoincareDualZeroGluing hU π hk hrigid b =
  LineBundle.SquareIsoFrames.lineBundleSquareTransportIso (U.scalarPoincareLine b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    ((Over.pullback b).map U.prescribedPoincareDualZero).left
    ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
    ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left
    (U.scalarPoincareDualZeroOverlap_source π b).symm
    (U.scalarPoincareDualZeroOverlap_target hU π hk hrigid b).symm
    (U.scalarPoincareNormalizedIso hU π hk hrigid b) := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualZeroGluing_preserves_frame_iso :
    U.scalarPoincareDualZeroGluing hU π hk hrigid b ≪≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).mapIso
        (U.scalarPoincareDualFrame b) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left) =
      ((Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).mapIso
        (U.scalarPoincareDualFrame b) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left) := by
  rw [U.scalarPoincareDualZeroGluing_def hU π hk hrigid b]
  exact LineBundle.ZeroGluing.lineBundleZeroGluing_preserves_frame (U.scalarPoincareLine b)
    ((Over.pullback b).map U.prescribedPoincareDualZero).left (U.scalarPoincareDualFrame b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
    ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left
    (U.scalarPoincareDualZeroOverlap_source π b) (U.scalarPoincareDualZeroOverlap_target hU π hk hrigid b)
    (U.scalarPoincareNormalizedIso hU π hk hrigid b) (U.scalarPoincareNormalizedIso_dual_native_frames hU π hk hrigid b)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualZeroGluing_preserves_frame :
    (U.scalarPoincareDualZeroGluing hU π hk hrigid b).hom ≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).mapIso
        (U.scalarPoincareDualFrame b) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left).hom =
      ((Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).mapIso
        (U.scalarPoincareDualFrame b) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left).hom := by
  exact LineBundle.ZeroGluingHom.iso_frame_hom _ _ _ (U.scalarPoincareDualZeroGluing_preserves_frame_iso hU π hk hrigid b)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
