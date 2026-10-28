import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CharacteristicZeroPolarizedRigidity

/-! # Frame Fine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameFine

noncomputable section

/-! Over a characteristic-zero field, the actual auxiliary-frame cover
of a fine prescribed-level PEL family is fine for both markings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace IntegralPELFrame
variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* K} {X : Over (Spec (.of K))}
    [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    (U : PEL.Has.IntegralPELObject P K iotaO N X) [NeZero L]
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))

theorem isFine (hN : 3 ≤ N) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hclass : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (A : PEL.Has.IntegralPELObject P K iotaO N T),
      ∃! f : T ⟶ X, Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data A.data))
    (T : Over (Spec (.of K))) [IsReduced T.left]
    (A : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO L N T) :
    ∃! j : T ⟶ FrameExistence.IntegralPELFrame.space U hL,
      Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((FrameExistence.IntegralPELFrame.universal U hL).pullback j) A) := by
  obtain ⟨f, ⟨e⟩, _⟩ := hclass T A.forgetAuxiliary
  obtain ⟨j, ⟨a⟩⟩ := FrameExistence.IntegralPELFrame.classifying_exists U hL A f e
  refine ⟨j, ⟨a⟩, ?_⟩
  rintro k ⟨b⟩
  apply FrameRigidity.IntegralPELFrame.classifying_unique U hL A (hclass T A.forgetAuxiliary) _ k j b a
  intro q e
  have : IsReduced (Over.mk q.left).left := inferInstanceAs (IsReduced T.left)
  exact CharacteristicZeroPolarizedRigidity.characteristicZero_polarized_reduced_rigidity X.hom U.data.polarized hN hPresentations
    (Over.mk q.left) e

end IntegralPELFrame

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameFine
