import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.LineLinearization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ScalarIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.Line
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CocycleMappedRelationDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryLineBundleDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent

/-! # Line Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Construct the actual Poincare line on a scalar-changed product
quotient directly from the original proved normalized relation. No
reducedness, normalization, or effectivity is assumed after scalar change. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)
    {S : Scheme.{0}} (b : S ⟶ Spec (.of R)) {Y : Over S}
    (q : (Over.pullback b).obj U.prescribedPoincareSpace ⟶ Y)
    (hq : IsKernelPair q.left ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
      ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.scalarPoincareLineDescentData :
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => q.left) := by
  let G := Over.pullback b ⋙ Over.map b
  let q₀ := (Over.map b).map q
  let src := DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
  let t := U.prescribedPoincareTarget π hU hk
  have hq₀ : IsKernelPair q₀ (G.map src) (G.map t) :=
    IsPullback.of_map (F := Over.forget _) (Over.OverMorphism.ext hq.w) hq
  let D := (U.prescribedPoincareLineLinearization hU π hk hrigid).mappedDescentData
    (Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks (Spec (.of R)))
    π U.prescribedPoincareProjection t (U.prescribedPoincareTarget_projection π hU hk)
    (U.prescribedPoincareTarget_normalized hU π hk hrigid)
    (U.prescribedPoincareTarget_cocycle hU π hk hrigid) U.prescribedPoincareLine.sheaf
    ((Scalar.Line.scalarTotalProjection b).app U.prescribedPoincareSpace) (G.map src) (G.map t)
    ((Scalar.Line.scalarTotalProjection b).app (U.prescribedPoincareOverlap π))
    ((Scalar.Line.scalarTotalProjection b).naturality src).symm ((Scalar.Line.scalarTotalProjection b).naturality t).symm q₀ hq₀
  exact Picard.PoincareBundle.UnderlyingDescent.underlyingDatum
    Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => q₀) D

variable [IsAffineHom q.left] [Flat q.left] [Surjective q.left] [IsLocallyNoetherian Y.left]

def IntegralAdded.PELId.IntegralAddedPELLevel.descendedScalarPoincareLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left :=
  OrdinaryLineBundleDescent.fpqcDescendedLineBundle q.left (U.scalarPoincareLineDescentData hU π hk hrigid b q hq)
    (U.scalarPoincareLine b).locallyTrivial

def IntegralAdded.PELId.IntegralAddedPELLevel.descendedScalarPoincareLinePullbackIso :
    ((U.descendedScalarPoincareLine hU π hk hrigid b q hq).pullback q.left).sheaf ≅
      (U.scalarPoincareLine b).sheaf :=
  OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso q.left (U.scalarPoincareLineDescentData hU π hk hrigid b q hq)
    (U.scalarPoincareLine b).locallyTrivial

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
