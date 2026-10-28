import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.DualFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.NormalizedIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.DualFrameInvariance

/-! # Dual -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! Native scalar dual-zero overlap equations and their actual
frames, for the same scalar Poincare gluing isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))

omit hU hk hrigid [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualZeroOverlap_source :
    ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left ≫
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left =
      ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left ≫
        ((Over.pullback b).map U.prescribedPoincareDualZero).left := by
  have h := congrArg (fun f => ((Over.pullback b).map f).left) (U.prescribedPoincareDualZeroOverlap_source π)
  simpa only [Functor.map_comp, Over.comp_left] using h

include hrigid in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualZeroOverlap_target :
    ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left ≫
        ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left =
      ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left ≫
        ((Over.pullback b).map U.prescribedPoincareDualZero).left := by
  have h := congrArg (fun f => ((Over.pullback b).map f).left) (U.prescribedPoincareDualZeroOverlap_target hU π hk hrigid)
  simpa only [Functor.map_comp, Over.comp_left] using h

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualSourceFrame :
    (((U.scalarPoincareLine b).pullback
      ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left).pullback
        ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback b).obj (U.prescribedOverlap π)).left :=
  LineBundle.SquareFrame.lineBundleSquareFrame (U.scalarPoincareLine b) ((Over.pullback b).map U.prescribedPoincareDualZero).left
    (U.scalarPoincareDualFrame b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
    (U.scalarPoincareDualZeroOverlap_source π b)

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualTargetFrame :
    (((U.scalarPoincareLine b).pullback ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left).pullback
        ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback b).obj (U.prescribedOverlap π)).left :=
  LineBundle.SquareFrame.lineBundleSquareFrame (U.scalarPoincareLine b) ((Over.pullback b).map U.prescribedPoincareDualZero).left
    (U.scalarPoincareDualFrame b) ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left
    ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left
    (U.scalarPoincareDualZeroOverlap_target hU π hk hrigid b)

end

section

/-! The actual scalar-transported Poincare isomorphism respects the
two adjusted frames along the scalar-transported dual-zero section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareNormalizedIso_dual_normalized :
    (Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left).mapIso
      (U.scalarPoincareNormalizedIso hU π hk hrigid b) ≪≫ U.scalarPoincareDualTargetFrame hU π hk hrigid b =
        U.scalarPoincareDualSourceFrame π b := by
  let F := Over.pullback b
  exact LineBundle.SquareIsoFrames.lineBundleSquareTransportIso_normalized U.prescribedPoincareLine U.prescribedPoincareDualZero.left
    U.prescribedPoincareCompatibleDualFrame
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left (U.prescribedPoincareTarget π hU hk).left
    (U.prescribedPoincareDualZeroOverlap π).left (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left
    (U.prescribedOverlapTarget hU π hk).left
    (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_source π))
    (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_target hU π hk hrigid))
    (U.prescribedPoincareNormalizedIso hU π hk hrigid)
    (U.prescribedPoincareNormalizedIso_dual_normalized hU π hk hrigid)
    (pullback.fst U.prescribedPoincareSpace.hom b) (F.map U.prescribedPoincareDualZero).left
    (pullback.fst U.prescribedTotalSpace.hom b)
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality U.prescribedPoincareDualZero))
    (pullback.fst (U.prescribedPoincareOverlap π).hom b) (F.map (U.prescribedPoincareDualZeroOverlap π)).left
    (pullback.fst (U.prescribedOverlap π).hom b)
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (U.prescribedPoincareDualZeroOverlap π)))
    (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left (F.map (U.prescribedPoincareTarget π hU hk)).left
    (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left (F.map (U.prescribedOverlapTarget hU π hk)).left
    (U.scalarPoincareDualZeroOverlap_source π b) (U.scalarPoincareDualZeroOverlap_target hU π hk hrigid b)
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)))
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (U.prescribedPoincareTarget π hU hk)))
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)))
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (U.prescribedOverlapTarget hU π hk)))

end

/-! Express the proved scalar dual-zero normalization in the native section-square
frames before specializing the frame-descent construction. -/

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareNormalizedIso_dual_native_frames :
    (Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left).mapIso
        (U.scalarPoincareNormalizedIso hU π hk hrigid b) ≪≫
      LineBundle.SquareFrame.lineBundleSquareFrame (U.scalarPoincareLine b) ((Over.pullback b).map U.prescribedPoincareDualZero).left
        (U.scalarPoincareDualFrame b) ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
        ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left
        ((Over.pullback b).map (U.prescribedOverlapTarget hU π hk)).left
        (U.scalarPoincareDualZeroOverlap_target hU π hk hrigid b) =
      LineBundle.SquareFrame.lineBundleSquareFrame (U.scalarPoincareLine b) ((Over.pullback b).map U.prescribedPoincareDualZero).left
        (U.scalarPoincareDualFrame b)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
        ((Over.pullback b).map (U.prescribedPoincareDualZeroOverlap π)).left
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection)).left
        (U.scalarPoincareDualZeroOverlap_source π b) := by
  simpa only [IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualTargetFrame, IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareDualSourceFrame] using
    U.scalarPoincareNormalizedIso_dual_normalized hU π hk hrigid b

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
