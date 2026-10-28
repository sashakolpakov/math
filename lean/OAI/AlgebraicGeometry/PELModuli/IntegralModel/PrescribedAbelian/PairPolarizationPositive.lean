import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairIntrinsicPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationPositiveTransport

/-! # Pair Polarization Positive -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The original ample polarization witness, transported through both
actual family comparisons, proves positivity of the descended map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_positive_local (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ ((Over.pullback b).obj X).left) :
    AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber ((B.dualData hrigid).pullback ((Over.pullback b).map π).left)
      ((Over.pullback ((Over.pullback b).map π).left).map (B.polarizationMap hrigid)) K t :=
  PolarizationPositiveTransport.positiveOnGeometricFiber_pairComparison
    (U.forgetAuxiliary.data.polarized.dual.pullback (pullback.fst X.hom b))
    ((B.dualData hrigid).pullback ((Over.pullback b).map π).left)
    ((Over.pullback (pullback.fst X.hom b)).map U.forgetAuxiliary.data.polarized.polarization.isogeny.hom)
    ((Over.pullback ((Over.pullback b).map π).left).map (B.polarizationMap hrigid))
    B.abelianNativeComparison B.dualNativeComparison (B.polarizationMap_native_comparison hrigid).symm
    (B.localPoincareNativeIso hrigid) t
    ((U.forgetAuxiliary.data.polarized.polarization.pullback (pullback.fst X.hom b)).positive K t)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_positive (K : Type) [Field K] [IsAlgClosed K]
    (t : Spec (.of K) ⟶ ((Over.pullback b).obj Q).left) :
    AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber (B.dualData hrigid) (B.polarizationMap hrigid) K t := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact PolarizationPositiveTransport.positiveOnGeometricFibers_of_baseChange (B.dualData hrigid) (B.polarizationMap hrigid)
    ((Over.pullback b).map π).left (B.polarizationMap_positive_local hrigid) K t

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
