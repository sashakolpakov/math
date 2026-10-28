import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLocalDualPoincare

/-! # Pair Local Poincare -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The restriction of the actual descended line is the actual Poincare
line of the constructed local dual representation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid) [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localPoincareLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle
    ((B.dual.pullback ((Over.pullback b).map π).left).scheme ⊗
      (B.abelian.pullback ((Over.pullback b).map π).left).scheme).left :=
  (B.poincareLine hrigid).pullback
    (PairBaseChangeProjection.pairBaseChangeProjection ((Over.pullback b).map π).left B.dual.scheme B.abelian.scheme)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localPoincareScalarIso : (B.localPoincareLine hrigid).sheaf ≅
    ((U.scalarPoincareLine b).pullback B.localProductComparison.inv.left).sheaf :=
  (Scheme.Modules.pullbackCongr B.localProductComparison_inv_cover.symm).app (B.poincareLine hrigid).sheaf ≪≫
  (Scheme.Modules.pullbackComp B.localProductComparison.inv.left B.productCover).symm.app
    (B.poincareLine hrigid).sheaf ≪≫
  (Scheme.Modules.pullback B.localProductComparison.inv.left).mapIso (B.poincareLinePullbackIso hrigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localPoincareIso : (B.localPoincareLine hrigid).sheaf ≅ B.localDualData.poincare.sheaf :=
  B.localPoincareScalarIso hrigid ≪≫ B.localDualPoincareScalarIso.symm

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localPoincare_homogeneous :
    (B.abelian.pullback ((Over.pullback b).map π).left).IsHomogeneousPicardClass
      (B.dual.pullback ((Over.pullback b).map π).left).scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B.localPoincareLine hrigid)) := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (B.localPoincareLine hrigid) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.localDualData.poincare := Quotient.sound ⟨B.localPoincareIso hrigid⟩
  rw [h]
  exact B.localDualData.poincareHomogeneous

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
