import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.QuotientFine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.QuotientFibers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange

/-! # Pair Scalar Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended polarized-action family classifies every
reduced-test integral PEL object over the new arithmetic coefficient ring.
Both existence and uniqueness use the original constructed quotient. -/

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
    [IsLocallyNoetherian ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q).left]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.scalarParent_classifies (hp : p.Prime) (hunit : IsUnit (p : R))
    (T : Over (Spec (.of R'))) [IsReduced T.left]
    (A : PEL.Has.IntegralPELObject P R' (φ.comp iotaO) N T) :
    ∃! d : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Q,
      Nonempty (PEL.Iso.PolarizedActionIso ((B.polarizedActionData hrigid).pullback d.left) A.data) := by
  let b := Spec.map (CommRingCat.ofHom φ)
  have : IsFinite ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (IsFinite π.left))
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  have hfine : (U.baseChange φ).IsFine := IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hU φ
  have hfib := U.reducedQuotientFibers_baseChange φ π (U.reducedQuotientFibers_of_kernelPair hU π hk)
  have hunit' : IsUnit (p : R') := by simpa only [map_natCast] using hunit.map φ
  exact (U.baseChange φ).reducedQuotient_isFine hfine ((Over.pullback b).map π) hfib
    (B.polarizedActionData hrigid) (B.polarizedActionComparison hrigid) hp hunit'
    (B.polarizedRigidity hrigid) T A

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
