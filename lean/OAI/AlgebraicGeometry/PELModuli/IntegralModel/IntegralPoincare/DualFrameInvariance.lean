import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.DualZeroNormalization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.OverlapBase
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.GlobalSquareFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedGlobalFrames
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.ZeroGluing

/-! # Dual Frame Invariance -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The adjusted dual-zero frame is preserved by the original
Poincare gluing, by normalization and the actual overlap rigidity. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualSourceGlobalFrame :
    ((U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).pullback
      (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U.prescribedOverlap π).left :=
  (Scheme.Modules.pullback (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left).mapIso
    U.prescribedPoincareCompatibleDualFrame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualTargetGlobalFrame :
    ((U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).pullback
      (U.prescribedOverlapTarget hU π hk).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U.prescribedOverlap π).left :=
  (Scheme.Modules.pullback (U.prescribedOverlapTarget hU π hk).left).mapIso
    U.prescribedPoincareCompatibleDualFrame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U.prescribedOverlapTarget hU π hk).left

omit hrigid [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualSourceFrame_section :
    LineBundle.SquareFrame.lineBundleSquareFrame (U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left)
        U.prescribedZero.left U.prescribedPoincareDualOriginFrame
        (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left (U.prescribedZeroOverlap hU π hk).left
        (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
        (congrArg Over.Hom.left (U.prescribedZeroOverlap_source hU π hk)) =
      (Scheme.Modules.pullback (U.prescribedZeroOverlap hU π hk).left).mapIso
        (U.prescribedPoincareDualSourceGlobalFrame π) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U.prescribedZeroOverlap hU π hk).left :=
  LineBundle.GlobalSquareFrame.lineBundleSquareFrame_global_of_normalized (U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left)
    U.prescribedPoincareCompatibleDualFrame U.prescribedZero.left U.prescribedPoincareDualOriginFrame
    (CategoryTheory.Iso.ext U.prescribedPoincareCompatibleDualFrame_origin)
    (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left (U.prescribedZeroOverlap hU π hk).left
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
    (congrArg Over.Hom.left (U.prescribedZeroOverlap_source hU π hk))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualTargetFrame_section :
    LineBundle.SquareFrame.lineBundleSquareFrame (U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left)
        U.prescribedZero.left U.prescribedPoincareDualOriginFrame (U.prescribedOverlapTarget hU π hk).left
        (U.prescribedZeroOverlap hU π hk).left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left
        (congrArg Over.Hom.left (U.prescribedZeroOverlap_target hU π hk hrigid)) =
      (Scheme.Modules.pullback (U.prescribedZeroOverlap hU π hk).left).mapIso
        (U.prescribedPoincareDualTargetGlobalFrame hU π hk) ≪≫
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (U.prescribedZeroOverlap hU π hk).left :=
  LineBundle.GlobalSquareFrame.lineBundleSquareFrame_global_of_normalized (U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left)
    U.prescribedPoincareCompatibleDualFrame U.prescribedZero.left U.prescribedPoincareDualOriginFrame
    (CategoryTheory.Iso.ext U.prescribedPoincareCompatibleDualFrame_origin)
    (U.prescribedOverlapTarget hU π hk).left (U.prescribedZeroOverlap hU π hk).left
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left
    (congrArg Over.Hom.left (U.prescribedZeroOverlap_target hU π hk hrigid))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZeroGluing_preserves_frame :
    U.prescribedPoincareDualZeroGluing hU π hk hrigid ≪≫ U.prescribedPoincareDualTargetGlobalFrame hU π hk =
      U.prescribedPoincareDualSourceGlobalFrame π := by
  have hn := U.prescribedPoincareDualZeroGluing_normalized hU π hk hrigid
  rw [U.prescribedPoincareDualSourceFrame_section hU π hk,
    U.prescribedPoincareDualTargetFrame_section hU π hk hrigid] at hn
  exact NormalizedGlobalFrames.normalizedIso_preserves_global_frames (U.prescribedOverlapBase hU π hk).left
    (U.prescribedZeroOverlap hU π hk).left (congrArg Over.Hom.left (U.prescribedZeroOverlap_baseProjection hU π hk))
    (U.prescribedOverlapBase_globalFunctions hU π hk)
    ((U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).pullback
      (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left)
    ((U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).pullback
      (U.prescribedOverlapTarget hU π hk).left)
    (U.prescribedPoincareDualSourceGlobalFrame π) (U.prescribedPoincareDualTargetGlobalFrame hU π hk)
    (U.prescribedPoincareDualZeroGluing hU π hk hrigid) hn

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareNormalizedIso_dual_normalized :
    (Scheme.Modules.pullback (U.prescribedPoincareDualZeroOverlap π).left).mapIso
        (U.prescribedPoincareNormalizedIso hU π hk hrigid) ≪≫
      LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareDualZero.left U.prescribedPoincareCompatibleDualFrame
        (U.prescribedPoincareTarget π hU hk).left (U.prescribedPoincareDualZeroOverlap π).left
        (U.prescribedOverlapTarget hU π hk).left
        (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_target hU π hk hrigid)) =
      LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareDualZero.left U.prescribedPoincareCompatibleDualFrame
        (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left (U.prescribedPoincareDualZeroOverlap π).left
        (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left
        (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_source π)) :=
  LineBundle.ZeroGluing.lineBundleZeroGluing_normalized U.prescribedPoincareLine U.prescribedPoincareDualZero.left
    U.prescribedPoincareCompatibleDualFrame
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left (U.prescribedPoincareTarget π hU hk).left
    (U.prescribedPoincareDualZeroOverlap π).left (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left
    (U.prescribedOverlapTarget hU π hk).left
    (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_source π))
    (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_target hU π hk hrigid))
    (U.prescribedPoincareNormalizedIso hU π hk hrigid) (U.prescribedPoincareDualZeroGluing_preserves_frame hU π hk hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
