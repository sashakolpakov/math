import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TotalSpace

/-! # Transport Normalization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual universal-family transport fixes the diagonal of the
quotient overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapTarget_normalized (hrigid : U.PrescribedRigid) :
    DescentCocycleChange.DescentCocycle.diagonal π U.prescribedProjection ≫ U.prescribedOverlapTarget hU π hk =
      𝟙 U.prescribedTotalSpace := by
  let a := U.prescribedProjection
  let f := DescentCocycleChange.DescentCocycle.source π a ≫ a
  let g := DescentCocycleChange.DescentCocycle.base π a
  let d := DescentCocycleChange.DescentCocycle.diagonal π a
  have h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π a
  have he : d ≫ f = d ≫ g := by
    dsimp only [d, f, g]
    rw [← Category.assoc, DescentCocycleChange.DescentCocycle.diagonal_source, Category.id_comp,
      DescentCocycleChange.DescentCocycle.diagonal_base]
  have hn := U.prescribedPointTransport_natural hU π hk hrigid f g h
    (DescentCocycleChange.DescentCocycle.source π a).left rfl d
  have hi := U.prescribedPointTransport_of_eq hU π hk hrigid (d ≫ f) (d ≫ g)
    (by simpa only [Category.assoc] using congrArg (fun m => d ≫ m) h) he
    (d.left ≫ (DescentCocycleChange.DescentCocycle.source π a).left) rfl
  apply Over.OverMorphism.ext
  exact hn.symm.trans (hi.trans
    (congrArg Over.Hom.left (DescentCocycleChange.DescentCocycle.diagonal_source π a)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
