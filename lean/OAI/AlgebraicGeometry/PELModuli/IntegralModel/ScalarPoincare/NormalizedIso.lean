import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.ZeroFrame
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.NormalizedIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareIsoFrames

/-! # Normalized Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual normalized Poincare isomorphism transported to the
literal scalar-changed relation, without assumptions on the new base. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareNormalizedIso :
    ((U.scalarPoincareLine b).pullback ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left).sheaf ≅
      ((U.scalarPoincareLine b).pullback ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left).sheaf :=
  LineBundle.SquareIsoFrames.lineBundleSquareTransportIso U.prescribedPoincareLine
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left (U.prescribedPoincareTarget π hU hk).left
    (pullback.fst U.prescribedPoincareSpace.hom b) (pullback.fst (U.prescribedPoincareOverlap π).hom b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)))
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (U.prescribedPoincareTarget π hU hk)))
    (U.prescribedPoincareNormalizedIso hU π hk hrigid)

omit hU hk hrigid [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left] [IsFinite π.left] [Etale π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareZeroOverlap_source :
    ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left ≫
        ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left =
      ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left ≫
        ((Over.pullback b).map U.prescribedPoincareZero).left := by
  have h := congrArg (fun f => ((Over.pullback b).map f).left) (U.prescribedPoincareZeroOverlap_source π)
  simpa only [Functor.map_comp, Over.comp_left] using h

include hrigid in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareZeroOverlap_target :
    ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left ≫
        ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left =
      ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left ≫
        ((Over.pullback b).map U.prescribedPoincareZero).left := by
  have h := congrArg (fun f => ((Over.pullback b).map f).left) (U.prescribedPoincareZeroOverlap_target hU π hk hrigid)
  simpa only [Functor.map_comp, Over.comp_left] using h

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareSourceFrame :
    (((U.scalarPoincareLine b).pullback
      ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left).pullback
        ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback b).obj (U.prescribedDualOverlap π)).left :=
  LineBundle.SquareFrame.lineBundleSquareFrame (U.scalarPoincareLine b) ((Over.pullback b).map U.prescribedPoincareZero).left
    (U.scalarPoincareZeroFrame b)
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
    ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left
    ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left
    (U.scalarPoincareZeroOverlap_source π b)

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareTargetFrame :
    (((U.scalarPoincareLine b).pullback ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left).pullback
        ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback b).obj (U.prescribedDualOverlap π)).left :=
  LineBundle.SquareFrame.lineBundleSquareFrame (U.scalarPoincareLine b) ((Over.pullback b).map U.prescribedPoincareZero).left
    (U.scalarPoincareZeroFrame b) ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left
    ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left
    ((Over.pullback b).map (U.prescribedDualOverlapTarget hU π hk)).left
    (U.scalarPoincareZeroOverlap_target hU π hk hrigid b)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
