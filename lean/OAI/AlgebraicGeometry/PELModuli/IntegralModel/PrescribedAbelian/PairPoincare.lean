import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairProduct
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScalarPoincare.LineDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryLineBundleRecovery

/-! # Pair Poincare -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Construct the Poincare line of the actual common-base abelian
pair, retaining its recovery as an isomorphism of full descent data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCoverOver_finite : IsFinite B.productCoverOver.left := inferInstanceAs (IsFinite B.productCover)
instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCoverOver_etale : Etale B.productCoverOver.left := inferInstanceAs (Etale B.productCover)
instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCoverOver_surjective : Surjective B.productCoverOver.left := inferInstanceAs (Surjective B.productCover)

variable (hrigid : U.PrescribedRigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLineDatum : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData
    (fun (_ : PUnit.{1}) => B.productCoverOver.left) :=
  U.scalarPoincareLineDescentData hU π hk hrigid b B.productCoverOver B.productCover_kernelPair

variable [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.productTotal.left :=
  OrdinaryLineBundleDescent.fpqcDescendedLineBundle B.productCoverOver.left (B.poincareLineDatum hrigid) (U.scalarPoincareLine b).locallyTrivial

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLinePullbackIso : ((B.poincareLine hrigid).pullback B.productCover).sheaf ≅ (U.scalarPoincareLine b).sheaf :=
  OrdinaryLineBundleDescent.fpqcDescendedLineBundlePullbackIso B.productCoverOver.left (B.poincareLineDatum hrigid)
    (U.scalarPoincareLine b).locallyTrivial

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLineDatumIso :
    Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum B.productCoverOver.left (B.poincareLine hrigid).sheaf ≅
      B.poincareLineDatum hrigid :=
  OrdinaryLineBundleRecovery.fpqcDescendedLineBundleDatumIso B.productCoverOver.left (B.poincareLineDatum hrigid)
    (U.scalarPoincareLine b).locallyTrivial

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.poincareLineDatumIso_component :
    (B.poincareLineDatumIso hrigid).hom.hom PUnit.unit = (B.poincareLinePullbackIso hrigid).hom :=
  OrdinaryLineBundleRecovery.fpqcDescendedLineBundleDatumIso_component B.productCoverOver.left (B.poincareLineDatum hrigid)
    (U.scalarPoincareLine b).locallyTrivial

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
