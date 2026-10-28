import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.CommonZeroOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.NormalizedIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareIsoFrames

/-! # Dual Zero Normalization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Restrict the Poincare gluing to the dual-zero line. The original
abelian-zero normalization proves its normalization at the common origin. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZeroGluing :
    ((U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).pullback
      (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left).sheaf ≅
    ((U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left).pullback
      (U.prescribedOverlapTarget hU π hk).left).sheaf :=
  LineBundle.SquareIsoFrames.lineBundleSquareTransportIso U.prescribedPoincareLine
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left (U.prescribedPoincareTarget π hU hk).left
    U.prescribedPoincareDualZero.left (U.prescribedPoincareDualZeroOverlap π).left
    (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left (U.prescribedOverlapTarget hU π hk).left
    (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_source π)).symm
    (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_target hU π hk hrigid)).symm
    (U.prescribedPoincareNormalizedIso hU π hk hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareDualZeroGluing_normalized :
    (Scheme.Modules.pullback (U.prescribedZeroOverlap hU π hk).left).mapIso
        (U.prescribedPoincareDualZeroGluing hU π hk hrigid) ≪≫
      LineBundle.SquareFrame.lineBundleSquareFrame (U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left)
        U.prescribedZero.left U.prescribedPoincareDualOriginFrame (U.prescribedOverlapTarget hU π hk).left
        (U.prescribedZeroOverlap hU π hk).left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left
        (congrArg Over.Hom.left (U.prescribedZeroOverlap_target hU π hk hrigid)) =
      LineBundle.SquareFrame.lineBundleSquareFrame (U.prescribedPoincareLine.pullback U.prescribedPoincareDualZero.left)
        U.prescribedZero.left U.prescribedPoincareDualOriginFrame
        (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left (U.prescribedZeroOverlap hU π hk).left
        (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
        (congrArg Over.Hom.left (U.prescribedZeroOverlap_source hU π hk)) := by
  exact LineBundle.SquareIsoFrames.lineBundleSquareTransportIso_normalized U.prescribedPoincareLine U.prescribedPoincareZero.left
    U.prescribedPoincareFrame
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left (U.prescribedPoincareTarget π hU hk).left
    (U.prescribedPoincareZeroOverlap π).left (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left
    (U.prescribedDualOverlapTarget hU π hk).left
    (congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_source π))
    (congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_target hU π hk hrigid))
    (U.prescribedPoincareNormalizedIso hU π hk hrigid)
    (CategoryTheory.Iso.ext (U.prescribedPoincareNormalizedIso_normalized hU π hk hrigid))
    U.prescribedPoincareDualZero.left U.prescribedZero.left U.prescribedDualZero.left
    (congrArg Over.Hom.left U.prescribedPoincare_commonZero)
    (U.prescribedPoincareDualZeroOverlap π).left (U.prescribedZeroOverlap hU π hk).left
    (U.prescribedDualZeroOverlap hU π hk).left (congrArg Over.Hom.left (U.prescribedPoincare_commonZeroOverlap hU π hk))
    (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left (U.prescribedOverlapTarget hU π hk).left
    (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left
    (congrArg Over.Hom.left (U.prescribedZeroOverlap_source hU π hk))
    (congrArg Over.Hom.left (U.prescribedZeroOverlap_target hU π hk hrigid))
    (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_source π)).symm
    (congrArg Over.Hom.left (U.prescribedPoincareDualZeroOverlap_target hU π hk hrigid)).symm
    (congrArg Over.Hom.left (U.prescribedDualZeroOverlap_source hU π hk)).symm
    (congrArg Over.Hom.left (U.prescribedDualZeroOverlap_target hU π hk hrigid)).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
