import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.FrameEquations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.ZeroGluingHom

/-! # Zero Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The scalar Poincare isomorphism induces a framed gluing
isomorphism on its actual abelian-zero line. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareZeroGluing :
    (((U.scalarPoincareLine b).pullback ((Over.pullback b).map U.prescribedPoincareZero).left).pullback
      ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).sheaf ≅
    (((U.scalarPoincareLine b).pullback ((Over.pullback b).map U.prescribedPoincareZero).left).pullback
      ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).sheaf :=
  LineBundle.SquareIsoFrames.lineBundleSquareTransportIso (U.scalarPoincareLine b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    ((Over.pullback b).map U.prescribedPoincareZero).left
    ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
    ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left
    (U.scalarPoincareZeroOverlap_source π b).symm
    (U.scalarPoincareZeroOverlap_target hU π hk hrigid b).symm
    (U.scalarPoincareNormalizedIso hU π hk hrigid b)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareZeroGluing_def : U.scalarPoincareZeroGluing hU π hk hrigid b =
  LineBundle.SquareIsoFrames.lineBundleSquareTransportIso (U.scalarPoincareLine b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    ((Over.pullback b).map U.prescribedPoincareZero).left
    ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
    ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left
    (U.scalarPoincareZeroOverlap_source π b).symm
    (U.scalarPoincareZeroOverlap_target hU π hk hrigid b).symm
    (U.scalarPoincareNormalizedIso hU π hk hrigid b) := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareZeroGluing_preserves_frame_iso :
    U.scalarPoincareZeroGluing hU π hk hrigid b ≪≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).mapIso
        (U.scalarPoincareZeroFrame b) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left) =
      ((Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).mapIso
        (U.scalarPoincareZeroFrame b) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left) := by
  rw [U.scalarPoincareZeroGluing_def hU π hk hrigid b]
  exact LineBundle.ZeroGluing.lineBundleZeroGluing_preserves_frame (U.scalarPoincareLine b)
    ((Over.pullback b).map U.prescribedPoincareZero).left (U.scalarPoincareZeroFrame b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
    ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left
    (U.scalarPoincareZeroOverlap_source π b) (U.scalarPoincareZeroOverlap_target hU π hk hrigid b)
    (U.scalarPoincareNormalizedIso hU π hk hrigid b) (U.scalarPoincareNormalizedIso_native_frames hU π hk hrigid b)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareZeroGluing_preserves_frame :
    (U.scalarPoincareZeroGluing hU π hk hrigid b).hom ≫
      ((Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).mapIso
        (U.scalarPoincareZeroFrame b) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left).hom =
      ((Scheme.Modules.pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).mapIso
        (U.scalarPoincareZeroFrame b) ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso
          ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left).hom := by
  exact LineBundle.ZeroGluingHom.iso_frame_hom _ _ _ (U.scalarPoincareZeroGluing_preserves_frame_iso hU π hk hrigid b)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
