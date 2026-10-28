import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.QuotientFibers

/-! # Quotient Fiber Condition -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The fiber relation of a prescribed quotient on reduced tests.
This records only equality of maps already lifting to the cover; it
contains no classifying-map or descended-family existence assertion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}

def IntegralAdded.PELId.IntegralAddedPELLevel.ReducedQuotientFibers (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (π : X ⟶ Q) : Prop :=
  ∀ (T : Over (Spec (.of R))) [IsReduced T.left] (f g : T ⟶ X),
    f ≫ π = g ≫ π ↔ Nonempty (PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f).data
      (U.forgetAuxiliary.pullback g).data)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.reducedQuotientFibers_of_kernelPair [NeZero L] [IsReduced X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine) (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) : U.ReducedQuotientFibers π := by
  intro T _ f g
  exact IntegralAuxiliary.QuotientFibers.IntegralAuxiliaryAction.quotient_eq_iff_prescribed_iso U hU π hk f g

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
