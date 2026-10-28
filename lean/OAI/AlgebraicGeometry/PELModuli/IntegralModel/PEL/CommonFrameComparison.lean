import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameFine
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameCharacteristicZero
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineSwap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineComparison

/-! # Common Frame Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameComparison

noncomputable section

/-! The two possible constructions of the common marked PEL space
are isomorphic, preserving the actual family and both full levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s L N : ℕ} [NeZero L] [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* K}
    {X Y : Over (Spec (.of K))} [IsReduced X.left] [IsReduced Y.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

theorem pel_common_frame_comparison
    (U : Has.IntegralPELObject P K iotaO N X) (A : Has.IntegralPELObject P K iotaO L Y)
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))
    (hN : ∀ y : Y.left, IsUnit (N : Y.left.presheaf.stalk y))
    (hN3 : 3 ≤ N) (hL3 : 3 ≤ L) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hU : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (B : Has.IntegralPELObject P K iotaO N T),
      ∃! f : T ⟶ X, Nonempty (Iso.PolarizedActionIso (U.pullback f).data B.data))
    (hA : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (B : Has.IntegralPELObject P K iotaO L T),
      ∃! f : T ⟶ Y, Nonempty (Iso.PolarizedActionIso (A.pullback f).data B.data)) :
    ∃ e : IntegralPEL.FrameExistence.IntegralPELFrame.space U hL ≅ IntegralPEL.FrameExistence.IntegralPELFrame.space A hN,
      Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso
        ((IntegralPEL.FrameExistence.IntegralPELFrame.universal A hN).swap.pullback e.hom) (IntegralPEL.FrameExistence.IntegralPELFrame.universal U hL)) := by
  have : IsReduced (IntegralPEL.FrameExistence.IntegralPELFrame.space U hL).left := IntegralPEL.FrameCharacteristicZero.IntegralPELFrame.characteristicZero_reduced U hL
  have : IsReduced (IntegralPEL.FrameExistence.IntegralPELFrame.space A hN).left := IntegralPEL.FrameCharacteristicZero.IntegralPELFrame.characteristicZero_reduced A hN
  exact IntegralAdded.FineComparison.integralAddedPEL_fine_comparison (IntegralPEL.FrameExistence.IntegralPELFrame.space U hL) (IntegralPEL.FrameExistence.IntegralPELFrame.space A hN)
    (IntegralPEL.FrameExistence.IntegralPELFrame.universal U hL) (IntegralPEL.FrameExistence.IntegralPELFrame.universal A hN).swap
    (IntegralPEL.FrameFine.IntegralPELFrame.isFine U hL hN3 hPresentations hU)
    (IntegralAdded.FineSwap.integralAddedPEL_fine_swap (IntegralPEL.FrameExistence.IntegralPELFrame.universal A hN) (IntegralPEL.FrameFine.IntegralPELFrame.isFine A hN hL3 hPresentations hA))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameComparison
