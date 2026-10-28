import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TotalSpace

/-! # Relation Points -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Evaluate the actual dual overlap transport on any reduced test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualOverlapTarget_natural (hrigid : U.PrescribedRigid) [IsReduced T.left]
    (k : T ⟶ U.prescribedDualOverlap π) :
    k.left ≫ (U.prescribedDualOverlapTarget hU π hk).left =
      U.prescribedDualPointTransport hU π hk
        (k ≫ (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualProjection))
        (k ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)
        (by
          simpa only [Category.assoc] using congrArg (fun m => k ≫ m)
            (DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualProjection))
        (k.left ≫ (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left) rfl :=
  (U.prescribedDualPointTransport_natural hU π hk hrigid
    (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualProjection)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)
    (DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualProjection)
    (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left rfl k).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
