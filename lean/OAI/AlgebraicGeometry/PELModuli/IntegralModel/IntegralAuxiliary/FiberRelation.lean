import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.ActionPoints
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.LabelTransitivity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FamilyFibers

/-! # Fiber Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.FiberRelation.IntegralAuxiliaryAction

noncomputable section

/-! Equal prescribed base maps differ by auxiliary labels on every
reduced test. The actual PEL family comparison constructs those labels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Y T : Over (Spec (.of R))}
    [IsReduced X.left] (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)

theorem homRelation_of_equal_prescribed_map (A : PEL.Has.IntegralPELObject P R iotaO N Y)
    (q : X ⟶ Y) (e : PEL.Iso.PolarizedActionIso (A.pullback q).data U.forgetAuxiliary.data)
    [IsReduced T.left] (f g : T ⟶ X) (h : f ≫ q = g ≫ q) :
    AbelianModuli.ReferenceFamily.RepresentedRelations.homRelation (ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L) (ActionSpace.IntegralAuxiliaryAction.target U hU) f g := by
  let a := IntegralPEL.FamilyFibers.prescribedFamilyFiberComparison A U.forgetAuxiliary q e f g h
  obtain ⟨b, ⟨eb⟩⟩ := IntegralAdded.PELId.IntegralAddedPELLevel.exists_relabel_of_prescribed_iso
    (U.pullback f) (U.pullback g) a
  apply (ActionPoints.IntegralAuxiliaryAction.homRelation_iff U hU f g).mpr
  refine ⟨b, ?_⟩
  have h1 := U.classifying_unique hU T (U.pullback g) (U.auxiliaryRelabelAt hU f b)
    ((U.auxiliaryRelabelAtComparison hU f b).trans eb)
  have h2 := U.classifying_unique hU T (U.pullback g) g (IntegralAdded.PELId.IntegralAddedPELLevel.Iso.refl _)
  exact h1.trans h2.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAuxiliary.FiberRelation.IntegralAuxiliaryAction
