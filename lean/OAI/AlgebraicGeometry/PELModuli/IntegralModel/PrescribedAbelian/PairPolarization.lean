import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationPositive
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationType

/-! # Pair Polarization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended dual data and isogeny carry the prescribed
polarization, with finite-flat type and geometric positivity both proved. -/

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

variable (hrigid : U.PrescribedRigid) [IsLocallyNoetherian ((Over.pullback b).obj Q).left]

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarization : AbelianModuli.HilbertConstruction.PolarizationData.Polarization (B.dualData hrigid) P.polarizationType where
  isogeny := B.polarizationIsogeny hrigid
  kernelType := B.polarizationIsogeny_type hrigid
  positive := B.polarizationMap_positive hrigid

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarization_isogeny : (B.polarization hrigid).isogeny = B.polarizationIsogeny hrigid := rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
