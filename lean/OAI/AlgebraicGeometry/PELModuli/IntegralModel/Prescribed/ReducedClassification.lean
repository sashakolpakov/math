import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairScalarClassification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairReducedObject
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FineDataReduction

/-! # Reduced Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The full integral PEL object constructed on the actual reduced
arithmetic quotient represents the prescribed problem on all reduced
test schemes. Its universal family is the genuine descended pullback. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s p N : ℕ} [NeZero p] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO p N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) p).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left}
    (φ : R →+* R') (B : U.PrescribedAbelianPair hU π hk (Spec.map (CommRingCat.ofHom φ)))
    (hrigid : U.PrescribedRigid)
    [IsNoetherian ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q).left]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.reducedPELObject_data : (B.reducedPELObject φ hrigid).data =
    (B.polarizedActionData hrigid).pullback
      (Reduction.reductionι ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q)).left := rfl

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.reducedPELObject_classifies (hp : p.Prime) (hunit : IsUnit (p : R))
    (T : Over (Spec (.of R'))) [IsReduced T.left]
    (A : PEL.Has.IntegralPELObject P R' (φ.comp iotaO) N T) :
    ∃! d : T ⟶ Reduction.reduction ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q),
      Nonempty (PEL.Iso.PolarizedActionIso ((B.reducedPELObject φ hrigid).pullback d).data A.data) := by
  have h := FineDataReduction.polarizedAction_classifies_reduction (B.polarizedActionData hrigid)
    (B.scalarParent_classifies φ hrigid hp hunit) T A
  change ∃! d : T ⟶ Reduction.reduction ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q),
    Nonempty (PEL.Iso.PolarizedActionIso ((B.reducedPELObject φ hrigid).data.pullback d.left) A.data)
  rw [B.reducedPELObject_data φ hrigid]
  exact h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
