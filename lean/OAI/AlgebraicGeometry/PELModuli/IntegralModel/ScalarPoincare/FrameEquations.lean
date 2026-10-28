import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.IsoNormalization

/-! # Frame Equations -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Express the proved scalar normalization in the native section-square
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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareNormalizedIso_native_frames :
    (Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left).mapIso
        (U.scalarPoincareNormalizedIso hU π hk hrigid b) ≪≫
      LineBundle.SquareFrame.lineBundleSquareFrame (U.scalarPoincareLine b) ((Over.pullback b).map U.prescribedPoincareZero).left
        (U.scalarPoincareZeroFrame b) ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
        ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left
        ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left
        (U.scalarPoincareZeroOverlap_target hU π hk hrigid b) =
      LineBundle.SquareFrame.lineBundleSquareFrame (U.scalarPoincareLine b) ((Over.pullback b).map U.prescribedPoincareZero).left
        (U.scalarPoincareZeroFrame b)
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
        ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
        (U.scalarPoincareZeroOverlap_source π b) := by
  simpa only [IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareTargetFrame, IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareSourceFrame] using
    U.scalarPoincareNormalizedIso_normalized hU π hk hrigid b

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
