import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairRosati
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLieRanks
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.CoefficientExtension

/-! # Pair Object -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended family is an integral PEL object: all of its
dual, polarization, full-level, action, Rosati, and Lie-rank fields are
constructed and proved on their common arithmetic quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left}

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.integralPELObjectOverOriginalBase {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)
    [IsReduced ((Over.pullback b).obj Q).left] [IsNoetherian ((Over.pullback b).obj Q).left] :
    PEL.Has.IntegralPELObject P R iotaO N ((Over.map b).obj ((Over.pullback b).obj Q)) where
  data := B.polarizedActionData hrigid
  rosati := B.rosati hrigid
  lieRanks := B.lieRanks hrigid

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.integralPELObject {R' : Type} [CommRing R'] (φ : R →+* R')
    (B : U.PrescribedAbelianPair hU π hk (Spec.map (CommRingCat.ofHom φ)))
    (hrigid : U.PrescribedRigid)
    [IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q).left]
    [IsNoetherian ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q).left] :
    PEL.Has.IntegralPELObject P R' (φ.comp iotaO) N
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q) :=
  (B.integralPELObjectOverOriginalBase hrigid).changeCoefficients φ

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
