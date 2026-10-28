import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.NormalizedIso

/-! # Iso Normalization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual scalar-transported Poincare isomorphism respects the
two frames along the scalar-transported abelian zero section. -/

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareNormalizedIso_normalized :
    (Scheme.Modules.pullback ((Over.pullback b).map (U.prescribedPoincareZeroOverlap π)).left).mapIso
      (U.scalarPoincareNormalizedIso hU π hk hrigid b) ≪≫ U.scalarPoincareTargetFrame hU π hk hrigid b =
        U.scalarPoincareSourceFrame π b := by
  let F := Over.pullback b
  exact LineBundle.SquareIsoFrames.lineBundleSquareTransportIso_normalized U.prescribedPoincareLine U.prescribedPoincareZero.left
    U.prescribedPoincareFrame
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left (U.prescribedPoincareTarget π hU hk).left
    (U.prescribedPoincareZeroOverlap π).left (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left
    (U.prescribedDualOverlapTarget hU π hk).left
    (congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_source π))
    (congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_target hU π hk hrigid))
    (U.prescribedPoincareNormalizedIso hU π hk hrigid)
    (Iso.ext (U.prescribedPoincareNormalizedIso_normalized hU π hk hrigid))
    (pullback.fst U.prescribedPoincareSpace.hom b) (F.map U.prescribedPoincareZero).left
    (pullback.fst U.prescribedDualTotalSpace.hom b)
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality U.prescribedPoincareZero))
    (pullback.fst (U.prescribedPoincareOverlap π).hom b) (F.map (U.prescribedPoincareZeroOverlap π)).left
    (pullback.fst (U.prescribedDualOverlap π).hom b)
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (U.prescribedPoincareZeroOverlap π)))
    (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left (F.map (U.prescribedPoincareTarget π hU hk)).left
    (F.map (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)).left (F.map (U.prescribedDualOverlapTarget hU π hk)).left
    (U.scalarPoincareZeroOverlap_source π b) (U.scalarPoincareZeroOverlap_target hU π hk hrigid b)
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)))
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (U.prescribedPoincareTarget π hU hk)))
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection)))
    (congrArg Over.Hom.left ((Scalar.Line.scalarTotalProjection b).naturality (U.prescribedDualOverlapTarget hU π hk)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
